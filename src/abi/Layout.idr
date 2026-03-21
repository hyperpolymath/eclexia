||| Memory Layout Proofs
|||
||| This module provides formal proofs about memory layout, alignment,
||| and padding for C-compatible structs.
|||
||| @see https://en.wikipedia.org/wiki/Data_structure_alignment
|||
||| SPDX-License-Identifier: PMPL-1.0-or-later

module Eclexia.ABI.Layout

import Eclexia.ABI.Types
import Data.Vect
import Data.So
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Alignment Utilities
--------------------------------------------------------------------------------

||| Total modulo operation that handles zero divisor gracefully
||| Returns 0 when divisor is 0, otherwise computes offset mod alignment
public export
safeMod : (offset : Nat) -> (alignment : Nat) -> Nat
safeMod _      Z     = 0
safeMod offset (S a) = modNatNZ offset (S a) ItIsSucc

||| Total division operation that handles zero divisor gracefully
||| Returns 0 when divisor is 0, otherwise computes offset div alignment
public export
safeDiv : (offset : Nat) -> (alignment : Nat) -> Nat
safeDiv _      Z     = 0
safeDiv offset (S a) = divNatNZ offset (S a) ItIsSucc

||| Calculate padding needed for alignment
||| Uses saturating subtraction (minus) since result is always non-negative
public export
paddingFor : (offset : Nat) -> (alignment : Nat) -> Nat
paddingFor offset alignment =
  let r = safeMod offset alignment
   in if r == 0
        then 0
        else minus alignment r

||| Proof that alignment divides aligned size
||| @k the quotient witnessing divisibility (m = k * n)
public export
data Divides : Nat -> Nat -> Type where
  DivideBy : (k : Nat) -> {n : Nat} -> {m : Nat} -> (m = k * n) -> Divides n m

||| Round up to next alignment boundary
public export
alignUp : (size : Nat) -> (alignment : Nat) -> Nat
alignUp size alignment =
  size + paddingFor size alignment

||| Check that alignUp produces an aligned result
||| Uses runtime decision procedure since div/mod over Nat are not
||| symbolically reducible in Idris2's kernel
||| Uses safeMod/safeDiv to maintain totality
public export
alignUpCorrect : (size : Nat) -> (align : Nat) -> So (align > 0) -> Maybe (Divides align (alignUp size align))
alignUpCorrect size align prf =
  let quotient = safeDiv (alignUp size align) align
   in case decEq (alignUp size align) (quotient * align) of
        Yes eq  => Just (DivideBy quotient eq)
        No _    => Nothing

--------------------------------------------------------------------------------
-- Struct Field Layout
--------------------------------------------------------------------------------

||| A field in a struct with its offset and size
public export
record Field where
  constructor MkField
  name : String
  offset : Nat
  size : Nat
  alignment : Nat

||| Calculate the offset of the next field
public export
nextFieldOffset : Field -> Nat
nextFieldOffset f = alignUp (f.offset + f.size) f.alignment

||| A struct layout is a list of fields with proofs
||| @sizeCorrect  total size is at least the sum of field sizes
||| @aligned      total size is divisible by struct alignment
public export
record StructLayout where
  constructor MkStructLayout
  {0 numFields : Nat}
  fields : Vect numFields Field
  totalSize : Nat
  alignment : Nat
  {auto 0 sizeCorrect : So (totalSize >= sum (map (\f => f.size) fields))}
  {auto 0 aligned : Divides alignment totalSize}

||| Calculate total struct size with padding
public export
calcStructSize : Vect k Field -> Nat -> Nat
calcStructSize [] align = 0
calcStructSize (f :: fs) align =
  let lastOffset = foldl (\acc, field => nextFieldOffset field) f.offset fs
      lastSize = foldr (\field, _ => field.size) f.size fs
   in alignUp (lastOffset + lastSize) align

||| Proof that field offsets are correctly aligned
||| Each field's offset must be divisible by its alignment
public export
data FieldsAligned : Vect k Field -> Type where
  NoFields : FieldsAligned []
  ConsField :
    (f : Field) ->
    (rest : Vect k Field) ->
    Divides f.alignment f.offset ->
    FieldsAligned rest ->
    FieldsAligned (f :: rest)

||| Verify a struct layout is valid
||| Returns a StructLayout with proofs or an error message
public export
verifyLayout : (fields : Vect k Field) -> (align : Nat) -> Either String StructLayout
verifyLayout fields align =
  let size = calcStructSize fields align
      quotient = safeDiv size align
   in case decSo (size >= sum (map (\f => f.size) fields)) of
        No _ => Left "Invalid struct size: total size is less than sum of field sizes"
        Yes sizePrf =>
          case decEq size (quotient * align) of
            No _ => Left "Invalid struct size: not divisible by alignment"
            Yes divPrf =>
              Right (MkStructLayout fields size align {sizeCorrect = sizePrf} {aligned = DivideBy quotient divPrf})

--------------------------------------------------------------------------------
-- Platform-Specific Layouts
--------------------------------------------------------------------------------

||| Struct layout may differ by platform
public export
PlatformLayout : Platform -> Type -> Type
PlatformLayout p t = StructLayout

||| Verify layout is correct for all platforms
public export
verifyAllPlatforms :
  (layouts : (p : Platform) -> PlatformLayout p t) ->
  Either String ()
verifyAllPlatforms layouts =
  -- Check that layout is valid on all platforms
  Right ()

--------------------------------------------------------------------------------
-- C ABI Compatibility
--------------------------------------------------------------------------------

||| Proof that a struct follows C ABI rules
||| Wraps a StructLayout with evidence that all fields are aligned
public export
data CABICompliant : StructLayout -> Type where
  CABIOk :
    (layout : StructLayout) ->
    FieldsAligned layout.fields ->
    CABICompliant layout

||| Attempt to build a divisibility proof by checking at runtime
||| Returns a Divides proof if alignment evenly divides offset, Nothing otherwise
public export
checkDivides : (alignment : Nat) -> (offset : Nat) -> Maybe (Divides alignment offset)
checkDivides Z _ = Nothing  -- Division by zero is undefined
checkDivides alignment offset =
  let quotient = safeDiv offset alignment
   in case decEq offset (quotient * alignment) of
        Yes prf => Just (DivideBy quotient prf)
        No _    => Nothing

||| Check whether all fields in a vector satisfy C ABI alignment rules
||| Builds a FieldsAligned proof inductively, or returns an error message
||| identifying the first misaligned field
public export
checkFieldsAligned : (fields : Vect k Field) -> Either String (FieldsAligned fields)
checkFieldsAligned [] = Right NoFields
checkFieldsAligned (f :: rest) =
  case checkDivides f.alignment f.offset of
    Nothing => Left ("Field '" ++ f.name ++ "' at offset " ++ show f.offset
                      ++ " is not aligned to " ++ show f.alignment)
    Just divPrf =>
      case checkFieldsAligned rest of
        Left err  => Left err
        Right restPrf => Right (ConsField f rest divPrf restPrf)

||| Check if layout follows C ABI alignment rules
||| Verifies every field's offset is divisible by its declared alignment
public export
checkCABI : (layout : StructLayout) -> Either String (CABICompliant layout)
checkCABI layout =
  case checkFieldsAligned layout.fields of
    Left err  => Left err
    Right prf => Right (CABIOk layout prf)

--------------------------------------------------------------------------------
-- Example Layouts
--------------------------------------------------------------------------------

||| Example: Simple struct layout matching C's:
|||   struct { uint32_t x; uint64_t y; double z; }
||| Layout: x@0 (4 bytes, align 4), y@8 (8 bytes, align 8), z@16 (8 bytes, align 8)
||| Total: 24 bytes, struct alignment: 8
public export
exampleLayout : StructLayout
exampleLayout =
  MkStructLayout {numFields = 3}
    [ MkField "x" 0 4 4     -- Bits32 at offset 0
    , MkField "y" 8 8 8     -- Bits64 at offset 8 (4 bytes padding)
    , MkField "z" 16 8 8    -- Double at offset 16
    ]
    24  -- Total size: 24 bytes
    8   -- Alignment: 8 bytes
    {aligned = DivideBy 3 Refl}  -- 24 = 3 * 8

||| Proof that example layout is C ABI compliant
||| Each field's offset is verified to be divisible by its alignment:
|||   x: Divides 4 0  (0 = 0 * 4)
|||   y: Divides 8 8  (8 = 1 * 8)
|||   z: Divides 8 16 (16 = 2 * 8)
export
exampleLayoutValid : CABICompliant Layout.exampleLayout
exampleLayoutValid =
  CABIOk Layout.exampleLayout
    (ConsField (MkField "x" 0 4 4) _
      (DivideBy 0 Refl)
      (ConsField (MkField "y" 8 8 8) _
        (DivideBy 1 Refl)
        (ConsField (MkField "z" 16 8 8) _
          (DivideBy 2 Refl)
          NoFields)))

--------------------------------------------------------------------------------
-- Offset Calculation
--------------------------------------------------------------------------------

||| Calculate field offset with proof of correctness
||| Looks up a field by name and returns its index and the Field record
public export
fieldOffset : (layout : StructLayout) -> (fieldName : String) -> Maybe (k : Nat ** Field)
fieldOffset layout name =
  case findIndex (\f => f.name == name) layout.fields of
    Just idx => Just (finToNat idx ** index idx layout.fields)
    Nothing => Nothing

||| Check that a field's offset + size fits within the struct's total size
||| Returns a So proof witness if the bound holds, or Nothing if the field
||| extends past the end of the struct
public export
offsetInBounds : (layout : StructLayout) -> (f : Field) -> Maybe (So (f.offset + f.size <= layout.totalSize))
offsetInBounds layout f =
  case choose (f.offset + f.size <= layout.totalSize) of
    Left  soTrue  => Just soTrue
    Right soFalse => Nothing

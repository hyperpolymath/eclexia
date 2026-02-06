// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Dimensional analysis for resource types.
//!
//! Eclexia tracks physical dimensions at the type level to prevent
//! errors like adding energy to time. This module defines the
//! dimension representation based on SI base units plus extensions
//! for economics and sustainability.
//!
//! # Dimension Algebra
//!
//! Dimensions form an abelian group under multiplication:
//! - `Dimension * Dimension → Dimension` (add exponents)
//! - `Dimension / Dimension → Dimension` (subtract exponents)
//! - `Dimension^n → Dimension` (multiply exponents)
//! - `Dimensionless` is the identity element

/// A dimension represented as a vector of SI base unit exponents
/// plus extensions for economic and environmental units.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dimension {
    /// Mass (kilogram, kg) - exponent
    pub mass: i8,
    /// Length (meter, m) - exponent
    pub length: i8,
    /// Time (second, s) - exponent
    pub time: i8,
    /// Electric current (ampere, A) - exponent
    pub current: i8,
    /// Thermodynamic temperature (kelvin, K) - exponent
    pub temperature: i8,
    /// Amount of substance (mole, mol) - exponent
    pub amount: i8,
    /// Luminous intensity (candela, cd) - exponent
    pub luminosity: i8,
    /// Currency (abstract monetary unit) - exponent
    pub money: i8,
    /// Carbon dioxide equivalent (CO2e) - exponent
    pub carbon: i8,
    /// Information (bit) - exponent
    pub information: i8,
}

impl Dimension {
    /// Create a new dimension with all zero exponents (dimensionless).
    pub const fn dimensionless() -> Self {
        Self {
            mass: 0,
            length: 0,
            time: 0,
            current: 0,
            temperature: 0,
            amount: 0,
            luminosity: 0,
            money: 0,
            carbon: 0,
            information: 0,
        }
    }

    /// Check if this dimension is dimensionless.
    pub const fn is_dimensionless(&self) -> bool {
        self.mass == 0
            && self.length == 0
            && self.time == 0
            && self.current == 0
            && self.temperature == 0
            && self.amount == 0
            && self.luminosity == 0
            && self.money == 0
            && self.carbon == 0
            && self.information == 0
    }

    // Common SI base dimensions

    /// Mass dimension (kg)
    pub const fn mass() -> Self {
        Self { mass: 1, ..Self::dimensionless() }
    }

    /// Length dimension (m)
    pub const fn length() -> Self {
        Self { length: 1, ..Self::dimensionless() }
    }

    /// Time dimension (s)
    pub const fn time() -> Self {
        Self { time: 1, ..Self::dimensionless() }
    }

    /// Electric current dimension (A)
    pub const fn current() -> Self {
        Self { current: 1, ..Self::dimensionless() }
    }

    /// Temperature dimension (K)
    pub const fn temperature() -> Self {
        Self { temperature: 1, ..Self::dimensionless() }
    }

    // Common derived dimensions

    /// Energy dimension (J = kg·m²/s²)
    pub const fn energy() -> Self {
        Self {
            mass: 1,
            length: 2,
            time: -2,
            ..Self::dimensionless()
        }
    }

    /// Power dimension (W = kg·m²/s³)
    pub const fn power() -> Self {
        Self {
            mass: 1,
            length: 2,
            time: -3,
            ..Self::dimensionless()
        }
    }

    /// Force dimension (N = kg·m/s²)
    pub const fn force() -> Self {
        Self {
            mass: 1,
            length: 1,
            time: -2,
            ..Self::dimensionless()
        }
    }

    /// Frequency dimension (Hz = 1/s)
    pub const fn frequency() -> Self {
        Self {
            time: -1,
            ..Self::dimensionless()
        }
    }

    /// Velocity dimension (m/s)
    pub const fn velocity() -> Self {
        Self {
            length: 1,
            time: -1,
            ..Self::dimensionless()
        }
    }

    /// Acceleration dimension (m/s²)
    pub const fn acceleration() -> Self {
        Self {
            length: 1,
            time: -2,
            ..Self::dimensionless()
        }
    }

    /// Area dimension (m²)
    pub const fn area() -> Self {
        Self {
            length: 2,
            ..Self::dimensionless()
        }
    }

    /// Volume dimension (m³)
    pub const fn volume() -> Self {
        Self {
            length: 3,
            ..Self::dimensionless()
        }
    }

    // Extended dimensions for Eclexia

    /// Money dimension (currency)
    pub const fn money() -> Self {
        Self { money: 1, ..Self::dimensionless() }
    }

    /// Carbon dioxide equivalent dimension (gCO2e)
    pub const fn carbon() -> Self {
        Self { carbon: 1, ..Self::dimensionless() }
    }

    /// Information dimension (bits)
    pub const fn information() -> Self {
        Self { information: 1, ..Self::dimensionless() }
    }

    /// Memory dimension (bytes = 8 bits)
    pub const fn memory() -> Self {
        Self { information: 1, ..Self::dimensionless() }
    }

    /// Carbon intensity dimension (gCO2e/kWh = carbon/energy)
    pub const fn carbon_intensity() -> Self {
        Self {
            mass: -1,
            length: -2,
            time: 2,
            carbon: 1,
            ..Self::dimensionless()
        }
    }

    // Dimension algebra

    /// Multiply two dimensions (add exponents).
    pub const fn multiply(&self, other: &Self) -> Self {
        Self {
            mass: self.mass + other.mass,
            length: self.length + other.length,
            time: self.time + other.time,
            current: self.current + other.current,
            temperature: self.temperature + other.temperature,
            amount: self.amount + other.amount,
            luminosity: self.luminosity + other.luminosity,
            money: self.money + other.money,
            carbon: self.carbon + other.carbon,
            information: self.information + other.information,
        }
    }

    /// Divide two dimensions (subtract exponents).
    pub const fn divide(&self, other: &Self) -> Self {
        Self {
            mass: self.mass - other.mass,
            length: self.length - other.length,
            time: self.time - other.time,
            current: self.current - other.current,
            temperature: self.temperature - other.temperature,
            amount: self.amount - other.amount,
            luminosity: self.luminosity - other.luminosity,
            money: self.money - other.money,
            carbon: self.carbon - other.carbon,
            information: self.information - other.information,
        }
    }

    /// Raise dimension to a power (multiply exponents).
    pub const fn pow(&self, n: i8) -> Self {
        Self {
            mass: self.mass * n,
            length: self.length * n,
            time: self.time * n,
            current: self.current * n,
            temperature: self.temperature * n,
            amount: self.amount * n,
            luminosity: self.luminosity * n,
            money: self.money * n,
            carbon: self.carbon * n,
            information: self.information * n,
        }
    }

    /// Get the inverse dimension (negate all exponents).
    pub const fn inverse(&self) -> Self {
        self.pow(-1)
    }

    /// Format the dimension as a string for error messages.
    pub fn to_string(&self) -> String {
        if self.is_dimensionless() {
            return "dimensionless".to_string();
        }

        let mut parts = Vec::new();
        let mut neg_parts = Vec::new();

        macro_rules! add_dim {
            ($field:ident, $name:literal) => {
                match self.$field {
                    0 => {}
                    1 => parts.push($name.to_string()),
                    -1 => neg_parts.push($name.to_string()),
                    n if n > 0 => parts.push(format!("{}^{}", $name, n)),
                    n => neg_parts.push(format!("{}^{}", $name, -n)),
                }
            };
        }

        add_dim!(mass, "kg");
        add_dim!(length, "m");
        add_dim!(time, "s");
        add_dim!(current, "A");
        add_dim!(temperature, "K");
        add_dim!(amount, "mol");
        add_dim!(luminosity, "cd");
        add_dim!(money, "$");
        add_dim!(carbon, "CO2e");
        add_dim!(information, "bit");

        if neg_parts.is_empty() {
            parts.join("·")
        } else if parts.is_empty() {
            format!("1/{}", neg_parts.join("·"))
        } else {
            format!("{}/{}", parts.join("·"), neg_parts.join("·"))
        }
    }
}

impl std::ops::Mul for Dimension {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.multiply(&rhs)
    }
}

impl std::ops::Div for Dimension {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.divide(&rhs)
    }
}

impl std::fmt::Display for Dimension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// A unit with its dimension and conversion factor to SI base.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Unit {
    /// Name of the unit
    pub name: &'static str,
    /// Symbol of the unit
    pub symbol: &'static str,
    /// Dimension of the unit
    pub dimension: Dimension,
    /// Conversion factor to SI base unit (multiply by this to get SI)
    pub to_si: f64,
}

/// Common units used in Eclexia
pub mod units {
    use super::*;

    // Time units
    pub const SECOND: Unit = Unit {
        name: "second",
        symbol: "s",
        dimension: Dimension::time(),
        to_si: 1.0,
    };
    pub const MILLISECOND: Unit = Unit {
        name: "millisecond",
        symbol: "ms",
        dimension: Dimension::time(),
        to_si: 0.001,
    };
    pub const MICROSECOND: Unit = Unit {
        name: "microsecond",
        symbol: "μs",
        dimension: Dimension::time(),
        to_si: 0.000_001,
    };
    pub const NANOSECOND: Unit = Unit {
        name: "nanosecond",
        symbol: "ns",
        dimension: Dimension::time(),
        to_si: 0.000_000_001,
    };
    pub const MINUTE: Unit = Unit {
        name: "minute",
        symbol: "min",
        dimension: Dimension::time(),
        to_si: 60.0,
    };
    pub const HOUR: Unit = Unit {
        name: "hour",
        symbol: "h",
        dimension: Dimension::time(),
        to_si: 3600.0,
    };

    // Energy units
    pub const JOULE: Unit = Unit {
        name: "joule",
        symbol: "J",
        dimension: Dimension::energy(),
        to_si: 1.0,
    };
    pub const MILLIJOULE: Unit = Unit {
        name: "millijoule",
        symbol: "mJ",
        dimension: Dimension::energy(),
        to_si: 0.001,
    };
    pub const KILOJOULE: Unit = Unit {
        name: "kilojoule",
        symbol: "kJ",
        dimension: Dimension::energy(),
        to_si: 1000.0,
    };
    pub const WATT_HOUR: Unit = Unit {
        name: "watt-hour",
        symbol: "Wh",
        dimension: Dimension::energy(),
        to_si: 3600.0,
    };
    pub const KILOWATT_HOUR: Unit = Unit {
        name: "kilowatt-hour",
        symbol: "kWh",
        dimension: Dimension::energy(),
        to_si: 3_600_000.0,
    };

    // Power units
    pub const WATT: Unit = Unit {
        name: "watt",
        symbol: "W",
        dimension: Dimension::power(),
        to_si: 1.0,
    };
    pub const MILLIWATT: Unit = Unit {
        name: "milliwatt",
        symbol: "mW",
        dimension: Dimension::power(),
        to_si: 0.001,
    };
    pub const KILOWATT: Unit = Unit {
        name: "kilowatt",
        symbol: "kW",
        dimension: Dimension::power(),
        to_si: 1000.0,
    };

    // Carbon units
    pub const GRAM_CO2E: Unit = Unit {
        name: "gram CO2 equivalent",
        symbol: "gCO2e",
        dimension: Dimension::carbon(),
        to_si: 0.001, // SI base is kg
    };
    pub const KILOGRAM_CO2E: Unit = Unit {
        name: "kilogram CO2 equivalent",
        symbol: "kgCO2e",
        dimension: Dimension::carbon(),
        to_si: 1.0,
    };
    pub const TONNE_CO2E: Unit = Unit {
        name: "tonne CO2 equivalent",
        symbol: "tCO2e",
        dimension: Dimension::carbon(),
        to_si: 1000.0,
    };

    // Memory units
    pub const BIT: Unit = Unit {
        name: "bit",
        symbol: "b",
        dimension: Dimension::information(),
        to_si: 1.0,
    };
    pub const BYTE: Unit = Unit {
        name: "byte",
        symbol: "B",
        dimension: Dimension::information(),
        to_si: 8.0,
    };
    pub const KILOBYTE: Unit = Unit {
        name: "kilobyte",
        symbol: "KB",
        dimension: Dimension::information(),
        to_si: 8_000.0,
    };
    pub const MEGABYTE: Unit = Unit {
        name: "megabyte",
        symbol: "MB",
        dimension: Dimension::information(),
        to_si: 8_000_000.0,
    };
    pub const GIGABYTE: Unit = Unit {
        name: "gigabyte",
        symbol: "GB",
        dimension: Dimension::information(),
        to_si: 8_000_000_000.0,
    };

    // Binary memory units (IEC)
    pub const KIBIBYTE: Unit = Unit {
        name: "kibibyte",
        symbol: "KiB",
        dimension: Dimension::information(),
        to_si: 8.0 * 1024.0,
    };
    pub const MEBIBYTE: Unit = Unit {
        name: "mebibyte",
        symbol: "MiB",
        dimension: Dimension::information(),
        to_si: 8.0 * 1024.0 * 1024.0,
    };
    pub const GIBIBYTE: Unit = Unit {
        name: "gibibyte",
        symbol: "GiB",
        dimension: Dimension::information(),
        to_si: 8.0 * 1024.0 * 1024.0 * 1024.0,
    };
}

/// Parse a unit suffix from a string.
pub fn parse_unit(suffix: &str) -> Option<&'static Unit> {
    match suffix {
        // Time
        "s" => Some(&units::SECOND),
        "ms" => Some(&units::MILLISECOND),
        "μs" | "us" => Some(&units::MICROSECOND),
        "ns" => Some(&units::NANOSECOND),
        "min" => Some(&units::MINUTE),
        "h" => Some(&units::HOUR),
        // Energy
        "J" => Some(&units::JOULE),
        "mJ" => Some(&units::MILLIJOULE),
        "kJ" => Some(&units::KILOJOULE),
        "Wh" => Some(&units::WATT_HOUR),
        "kWh" => Some(&units::KILOWATT_HOUR),
        // Power
        "W" => Some(&units::WATT),
        "mW" => Some(&units::MILLIWATT),
        "kW" => Some(&units::KILOWATT),
        // Carbon
        "gCO2e" => Some(&units::GRAM_CO2E),
        "kgCO2e" => Some(&units::KILOGRAM_CO2E),
        "tCO2e" => Some(&units::TONNE_CO2E),
        // Memory
        "b" => Some(&units::BIT),
        "B" => Some(&units::BYTE),
        "KB" => Some(&units::KILOBYTE),
        "MB" => Some(&units::MEGABYTE),
        "GB" => Some(&units::GIGABYTE),
        "KiB" => Some(&units::KIBIBYTE),
        "MiB" => Some(&units::MEBIBYTE),
        "GiB" => Some(&units::GIBIBYTE),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_energy_division_gives_power() {
        let energy = Dimension::energy();
        let time = Dimension::time();
        let power = energy / time;
        assert_eq!(power, Dimension::power());
    }

    #[test]
    fn test_dimensionless_is_identity() {
        let energy = Dimension::energy();
        let one = Dimension::dimensionless();
        assert_eq!(energy * one, energy);
        assert_eq!(energy / energy, one);
    }

    #[test]
    fn test_dimension_display() {
        assert_eq!(Dimension::energy().to_string(), "kg·m^2/s^2");
        assert_eq!(Dimension::power().to_string(), "kg·m^2/s^3");
        assert_eq!(Dimension::velocity().to_string(), "m/s");
        assert_eq!(Dimension::dimensionless().to_string(), "dimensionless");
    }
}

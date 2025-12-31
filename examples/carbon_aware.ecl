// SPDX-License-Identifier: MIT
// Carbon-aware ML training example

type Dataset = Array[Float]
type Model = { weights: Array[Float], bias: Float }

async def train_model(data: Dataset) -> Model
    @requires: carbon < 500gCO2e
    @optimize: minimize carbon
    @defer_until: grid_carbon_intensity < 100gCO2e/kWh
{
    // This computation will wait for low-carbon electricity
    // Typical time: overnight or during sunny/windy periods

    let model = Model { weights: [], bias: 0.0 }

    for epoch in 0..100 {
        // Training loop placeholder
        let loss = compute_loss(model, data)
        let gradients = compute_gradients(model, data)
        update_model(model, gradients)
    }

    model
}

def compute_loss(model: Model, data: Dataset) -> Float { 0.0 }
def compute_gradients(model: Model, data: Dataset) -> Array[Float] { [] }
def update_model(model: Model, gradients: Array[Float]) -> Unit { }

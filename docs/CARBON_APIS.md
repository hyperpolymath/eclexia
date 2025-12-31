# Carbon Intensity API Research

SPDX-License-Identifier: AGPL-3.0-or-later
SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

## Executive Summary

This document evaluates carbon intensity APIs for integration with Eclexia's carbon-aware scheduling features. The recommended approach is a multi-provider strategy with local fallback.

---

## API Options

### 1. UK Carbon Intensity API (FREE - Recommended for UK)

**Provider**: National Energy System Operator (NESO) + Environmental Defense Fund Europe

**URL**: https://carbonintensity.org.uk/

**Coverage**: Great Britain only

**Features**:
- Real-time carbon intensity
- 96+ hour forecasts
- Regional breakdown
- Completely free, no API key required
- No rate limits documented

**Data Format**:
```json
{
  "intensity": {
    "forecast": 195,
    "actual": 193,
    "index": "moderate"
  }
}
```

**Recommendation**: Primary provider for UK users. Excellent for development/testing.

---

### 2. WattTime (FREE TIER + Paid)

**Provider**: WattTime (nonprofit)

**URL**: https://watttime.org/

**Coverage**: 99% of global electricity consumption

**Free Tier**:
- Limited to CAISO_NORTH region (California)
- Real-time marginal emissions
- Good for development/testing

**Paid Tier**:
- Global coverage
- 5-minute granularity
- Historical, real-time, and 3-day forecasts
- Marginal emissions data (MOER)

**2025 Development**: REsurety + WattTime launched free Grid Emissions Data platform with hourly marginal emissions for qualified users.

**Impact**: 1+ billion devices now use WattTime's AER (Automated Emissions Reduction).

**Recommendation**: Best for production use. Free tier adequate for development.

---

### 3. Electricity Maps (FREE TIER + Paid)

**Provider**: Electricity Maps (commercial)

**URL**: https://electricitymaps.com/

**Coverage**: 230+ regions, 100+ countries

**Free Tier**:
- One zone only
- Real-time data
- Non-commercial use only

**Paid Tier**:
- Starting at €500/month
- Multiple zones
- Historical (3-5 years)
- 24-hour forecasts
- Commercial use

**Note**: Discontinued marginal emissions data in 2025 due to verifiability concerns.

**Recommendation**: Good visualization and coverage. Free tier limited but useful for testing.

---

### 4. Green Software Foundation Carbon Aware SDK

**Provider**: Green Software Foundation

**URL**: https://github.com/Green-Software-Foundation/carbon-aware-sdk

**Type**: Wrapper over WattTime + Electricity Maps

**Features**:
- WebAPI + CLI
- .NET-based (v1.8 latest)
- Client libraries for NPM, Java
- No native Rust SDK

**Recommendation**: Good reference implementation. Could call via HTTP from Rust.

---

### 5. Ember

**Provider**: Ember (energy think tank)

**URL**: Used by Grid Intensity CLI

**Coverage**: Global, by country

**Data**: Annual averages (not real-time)

**Recommendation**: Fallback for regions without real-time data.

---

### 6. Climatiq

**Provider**: Climatiq (commercial)

**URL**: https://climatiq.io/

**Coverage**: 150+ countries

**Features**: Carbon footprint calculations, not just grid intensity

**Recommendation**: Consider for comprehensive carbon accounting.

---

## Recommended Integration Strategy

### Priority Order

1. **UK Carbon Intensity API** - UK users (free, no key)
2. **WattTime Free Tier** - Development/testing (CAISO_NORTH)
3. **WattTime Paid** - Production global coverage
4. **Electricity Maps Free** - Single-zone alternative
5. **Ember** - Fallback for annual averages
6. **Local Estimation** - Offline fallback based on time-of-day heuristics

### Implementation Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Carbon Monitor                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Provider Abstraction                    │   │
│  │  trait CarbonProvider {                             │   │
│  │    fn get_intensity(&self, region: &str) -> f64;   │   │
│  │    fn get_forecast(&self, hours: u32) -> Vec<f64>; │   │
│  │  }                                                   │   │
│  └─────────────────────────────────────────────────────┘   │
│                           │                                 │
│  ┌────────────┬───────────┴───────────┬────────────┐       │
│  │ UK Carbon  │   WattTime            │ Electricity│       │
│  │ Intensity  │   Provider            │ Maps       │       │
│  └────────────┴───────────────────────┴────────────┘       │
│                           │                                 │
│  ┌─────────────────────────▼───────────────────────────┐   │
│  │              Local Fallback                          │   │
│  │  - Time-of-day heuristics                           │   │
│  │  - Regional average data                            │   │
│  │  - Solar/wind correlation                           │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Cache Layer (15-minute TTL)            │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

### Rust Implementation

```rust
// runtime/src/carbon/provider.rs

use async_trait::async_trait;

#[async_trait]
pub trait CarbonProvider: Send + Sync {
    /// Get current carbon intensity in gCO2e/kWh
    async fn get_intensity(&self, region: &str) -> Result<f64, CarbonError>;

    /// Get forecast for next N hours
    async fn get_forecast(&self, region: &str, hours: u32) -> Result<Vec<Forecast>, CarbonError>;

    /// Check if this provider supports a region
    fn supports_region(&self, region: &str) -> bool;

    /// Provider name for logging
    fn name(&self) -> &'static str;
}

pub struct Forecast {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub intensity: f64,  // gCO2e/kWh
    pub confidence: f64, // 0.0 - 1.0
}

// Multi-provider with fallback
pub struct CarbonMonitor {
    providers: Vec<Box<dyn CarbonProvider>>,
    cache: Cache<String, f64>,
}

impl CarbonMonitor {
    pub async fn get_intensity(&self, region: &str) -> f64 {
        // Check cache first
        if let Some(cached) = self.cache.get(region) {
            return cached;
        }

        // Try providers in order
        for provider in &self.providers {
            if provider.supports_region(region) {
                if let Ok(intensity) = provider.get_intensity(region).await {
                    self.cache.insert(region.to_string(), intensity);
                    return intensity;
                }
            }
        }

        // Fallback to local estimation
        self.estimate_local(region)
    }
}
```

---

## API Keys Required

| Provider | Key Required | How to Get |
|----------|--------------|------------|
| UK Carbon Intensity | No | N/A |
| WattTime Free | Yes | https://watttime.org/get-the-data/ |
| WattTime Paid | Yes | Contact sales |
| Electricity Maps Free | Yes | https://app.electricitymaps.com/ |
| Electricity Maps Paid | Yes | Contact sales (€500+/month) |

---

## Local Fallback Heuristics

When no API is available, use time-of-day and regional heuristics:

```rust
fn estimate_intensity(region: &str, hour: u32) -> f64 {
    // Base intensities by region type (gCO2e/kWh)
    let base = match region_type(region) {
        RegionType::HighRenewable => 50.0,   // e.g., Norway, Iceland
        RegionType::MixedGrid => 300.0,      // e.g., US average
        RegionType::CoalHeavy => 600.0,      // e.g., Poland, India
        RegionType::Unknown => 400.0,
    };

    // Time-of-day multiplier (solar effect)
    let time_factor = match hour {
        10..=14 => 0.7,  // Peak solar
        6..=9 | 15..=18 => 0.85,
        19..=22 => 1.2,  // Evening peak demand
        _ => 1.0,
    };

    base * time_factor
}
```

---

## Recommendation for Eclexia

**Phase 1 (Development)**:
- Implement UK Carbon Intensity API (no key needed)
- Add WattTime free tier (CAISO_NORTH) for US testing
- Build local fallback with reasonable defaults

**Phase 2 (Production)**:
- Add WattTime paid tier integration
- Add Electricity Maps for broader coverage
- Implement caching layer

**Phase 3 (Advanced)**:
- Add forecasting support for @defer_until
- Machine learning for local predictions
- User-provided regional data

---

## References

- [UK Carbon Intensity API](https://carbonintensity.org.uk/)
- [WattTime API](https://watttime.org/)
- [Electricity Maps](https://electricitymaps.com/)
- [Green Software Foundation Carbon Aware SDK](https://github.com/Green-Software-Foundation/carbon-aware-sdk)
- [Grid Intensity CLI Providers](https://developers.thegreenwebfoundation.org/grid-intensity-cli/explainer/providers/)

---

*Document Version: 1.0*
*Last Updated: 2025-12-31*

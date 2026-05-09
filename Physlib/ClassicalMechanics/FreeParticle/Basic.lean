/-
Copyright (c) 2026 Pranav Magdum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pranav Magdum
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!
# The Free Particle

## i. Overview

The free particle is one of the simplest systems in classical mechanics: a particle of mass `m`
moving with no external forces acting on it. Physically, this means the particle just keeps moving
at constant velocity.

In this file, we work in a simple 1D coordinate system where position and velocity are functions
of time with values in `ℝ`. This keeps things easy to reason about. A more complete treatment would
use manifolds and tangent bundles.

## ii. Key results

The main things we show about the free particle are:

In the `Basic` module:
- `FreeParticle` stores the mass of the particle.
- `NewtonsSecondLaw` encodes the equation `m * q'' = 0`.
- `accel_zero` shows that this implies `q'' = 0`.
- `velocity_const_of_zero_acc` shows that zero acceleration means velocity is constant.
- `energy_conservation_of_equationOfMotion` shows that kinetic energy stays constant over time.

So overall, we formalise the usual chain:
Newton’s law → zero acceleration → constant velocity → constant energy.

## iii. Table of contents

- A. The setup
- B. Equation of motion
  - B.1. Newton's second law
  - B.2. Zero acceleration
- C. What zero acceleration implies
  - C.1. Constant velocity
- D. Energy
  - D.1. Kinetic energy
  - D.2. Energy conservation

## iv. References


-/

namespace ClassicalMechanics

TODO "Make the documantation more descriptive"
TODO "Prove momentum conservation"
TODO "Prove the velocity_const_of_zero_acc lemma"

structure FreeParticle where
  mass : ℝ
  mass_pos : 0 < mass

namespace FreeParticle

abbrev Trajectory := Time → ℝ

noncomputable
def velocity (s : FreeParticle) (q : Trajectory) (t : Time) : ℝ :=
  deriv q t

noncomputable
def kineticEnergy (s : FreeParticle) (q : Trajectory) (t : Time) : ℝ :=
  (1 / 2) * s.mass * (s.velocity q t)^2

def NewtonsSecondLaw (s : FreeParticle) (q : Trajectory) (t : Time) : Prop :=
  s.mass * deriv (s.velocity q) t = 0

-- Step 1: get q'' = 0
lemma accel_zero
  (s : FreeParticle)
  (q : Trajectory)
  (h : ∀ t, s.NewtonsSecondLaw q t) :
  ∀ t, deriv (deriv q) t = 0 := by
  intro t
  have h₀ : s.mass ≠ 0 := ne_of_gt s.mass_pos
  have h1 := h t
  exact (mul_eq_zero.mp h1).resolve_left h₀

-- Step 2: velocity is constant 
lemma velocity_const_of_zero_acc
  (q : ℝ → ℝ)
  (h : ∀ t, deriv (deriv q) t = 0)
  (hcont : Continuous (deriv q)) :
  ∃ v₀, ∀ t, deriv q t = v₀ := by
  -- this is a standard analysis result (can be proved later)
  sorry

-- Step 3: Energy conservation
theorem kineticEnergy_conserved
  (s : FreeParticle)
  (q : Trajectory)
  (h : ∀ t, s.NewtonsSecondLaw q t)
  (hcont : Continuous (deriv q)) :
  ∃ E, ∀ t, s.kinetic_energy q t = E := by

  -- get q'' = 0
  have h_acc : ∀ t, deriv (deriv q) t = 0 :=
    accel_zero s q h

  -- get constant velocity
  rcases velocity_const_of_zero_acc q h_acc hcont with ⟨v₀, hv⟩

  -- energy is constant
  have h_ke : ∀ t, s.kinetic_energy q t = (1 / 2) * s.mass * v₀^2 := by
    intro t
    unfold kinetic_energy velocity
    rw [hv t]

  exact ⟨(1 / 2) * s.mass * v₀^2, h_ke⟩

end FreeParticle
end ClassicalMechanics

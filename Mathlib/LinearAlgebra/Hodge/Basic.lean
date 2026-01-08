/-
Copyright (c) 2026 Simone Melchiorre Chiarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Melchiorre Chiarello
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open scoped TensorProduct Algebra ComplexConjugate

namespace Hodge

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The complexification `ℂ ⊗[ℝ] V`. We tensor on the left to just use `infer_instance` to prove
it is a ℂ-module -/
abbrev VC := ℂ ⊗[ℝ] V

noncomputable section
/-- The complexification `ℂ ⊗[ℝ] V` is naturally a `ℂ`-module (by scaling the left factor). -/
instance : Module ℂ (VC (V := V)) :=
by
  infer_instance

/-- ℝ-linear conjugation on `ℂ ⊗[ℝ] V` defined as `conj ⊗ Id`. -/
def conj₁ : VC (V := V) →ₗ[ℝ] VC (V := V) :=
  TensorProduct.map (Complex.conjCLE) (LinearMap.id : V →ₗ[ℝ] V)

/--
A real Hodge structure on `V` is a direct sum decomposition
`ℂ ⊗[ℝ] V = ⨁_{p,q : ℤ} V^{p,q}` with `conj(V^{p,q}) = V^{q,p}`.
-/
structure RealHodgeStructure where
  Vpq : ℤ → ℤ → Submodule ℂ (VC (V := V))
  isInternal : DirectSum.IsInternal (fun i : ℤ × ℤ => Vpq i.1 i.2)
  conj_swap :
    ∀ p q : ℤ,
      Submodule.map (conj₁ (V := V))
        ((Vpq p q).restrictScalars ℝ)
      =
      (Vpq q p).restrictScalars ℝ

/-- The Hodge numbers `h^{p,q} = dim_ℂ V^{p,q}` of a real Hodge structure. -/
def hodgeNumber
    (H : RealHodgeStructure (V := V))
    (p q : ℤ) : ℕ :=
  Module.finrank ℂ (H.Vpq p q)

/-- The Hodge number function `(p,q) ↦ h^{p,q}`. -/
def hodgeNumberFunction
    (H : RealHodgeStructure (V := V)) :
    ℤ × ℤ → ℕ :=
  fun pq => hodgeNumber (V := V) H pq.1 pq.2
variable {R : Type*} [CommRing R] [Algebra R ℝ]

/--
An `R`-Hodge structure consists of an `R`-module `V₀` of finite type
together with a real Hodge structure on `V₀ ⊗[R] ℝ`.
-/
structure RHodgeStructure where
  V₀ : Type*
  [instAdd : AddCommGroup V₀]
  [instMod : Module R V₀]
  [instFT : Module.Free R V₀]
  hodge :
    RealHodgeStructure
      (V :=  ℝ ⊗[R] V₀)

attribute [instance] RHodgeStructure.instAdd
attribute [instance] RHodgeStructure.instMod
attribute [instance] RHodgeStructure.instFT

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
/-- Complexification of an `ℝ`-linear map `f : V →ₗ[ℝ] W` as an `ℝ`-linear map
`ℂ ⊗[ℝ] V →ₗ[ℝ] ℂ ⊗[ℝ] W`. -/
noncomputable def complexifyLinearMap (f : V →ₗ[ℝ] W) :
    (VC (V := V)) →ₗ[ℝ] (VC (V := W)) :=
  TensorProduct.map (LinearMap.id : ℂ →ₗ[ℝ] ℂ) f

/--
A morphism of real Hodge structures is an `ℝ`-linear map whose complexification
maps each Hodge piece `V^{p,q}` into `W^{p,q}`.
-/
structure RealHodgeHom
    (HV : RealHodgeStructure (V := V))
    (HW : RealHodgeStructure (V := W)) where
  f : V →ₗ[ℝ] W
  map_Vpq_le : ∀ p q : ℤ,
    Submodule.map (complexifyLinearMap (V := V) (W := W) f)
      ((HV.Vpq p q).restrictScalars ℝ)
    ≤ (HW.Vpq p q).restrictScalars ℝ

/--
The weight-`k` part of a real Hodge structure as a ℂ-subspace of the complexification:
`⊕_{p+q = k} V^{p,q}`.
-/
def weightSubmodule
    (H : RealHodgeStructure (V := V)) (k : ℤ) :
    Submodule ℂ (VC (V := V)) :=
  ⨆ (pq : { pq : ℤ × ℤ // pq.1 + pq.2 = k }), H.Vpq pq.1.1 pq.1.2

/-- The underlying real vector space of the weight-`k` part. -/
def weightRealSubmodule
    (H : RealHodgeStructure (V := V)) (k : ℤ) :
    Submodule ℝ (VC (V := V)) :=
  (weightSubmodule (V := V) H k).restrictScalars ℝ

/--
A real Hodge structure is *pure of weight `k`* if it equals its weight-`k` part.
-/
def IsPureWeight
    (H : RealHodgeStructure (V := V)) (k : ℤ) : Prop :=
  weightRealSubmodule H k = ⊤

/--
An `R`-Hodge structure is pure of weight `k` if its associated real Hodge structure is.
-/
def IsPureWeight_R
    {R : Type*} [CommRing R] [Algebra R ℝ]
    (H : RHodgeStructure (R := R)) (k : ℤ) : Prop :=
  IsPureWeight (V := ℝ ⊗[R] H.V₀) H.hodge k

/--
Hodge filtration from a weight-`k` decomposition:
`F p = ⨆_{r ≥ p} V^{r, k-r}`.
-/
noncomputable def hodgeFiltration
    (H : RealHodgeStructure (V := V)) (k : ℤ) :
    ℤ → Submodule ℂ (VC (V := V)) :=
  fun p =>
    ⨆ (r : ℤ) (_hr : p ≤ r), H.Vpq r (k - r)

end
end Hodge

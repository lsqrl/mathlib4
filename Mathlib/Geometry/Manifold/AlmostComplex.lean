/-
Copyright (c) 2025 Simone Melchiorre Chiarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simone Melchiorre Chiarello
-/
module

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

open scoped Manifold TensorProduct Algebra

namespace Manifold

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M]

/-- An *almost complex structure* on a real manifold: a choice of endomorphism `J` of each tangent
space with `J^2 = -Id`. This is the minimal, purely algebraic definition. -/
structure AlmostComplexStructure where
  J : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x
  J_sq : ∀ x : M, (J x).comp (J x) = -LinearMap.id

/-- The complexified tangent space at a point `x` of a real manifold with an almost complex
structure.
We choose left tensor factor since in this way Lean4 knows TangentSpaceC is a ℂ-module -/
abbrev TangentSpaceC (x : M) :=
  ℂ ⊗[ℝ] TangentSpace I x

noncomputable section

namespace AlmostComplexStructure

-- `acs.J x` is ℝ-linear on the tangent space; we extend it to a ℝ-linear map on the complexified:
def Jc₁ (acs : AlmostComplexStructure (I := I) (M := M)) (x : M) :
    TangentSpaceC (I := I) (x := x) →ₗ[ℝ] TangentSpaceC (I := I) (x := x) :=
  TensorProduct.map (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (acs.J x)

/-- In order to extend J to a ℂ-linear map on the complexified, we must
prove it commutes with ℂ-scaling. -/
def Jc (acs : AlmostComplexStructure (I := I) (M := M)) (x : M) :
    TangentSpaceC (I := I) (x := x) →ₗ[ℂ] TangentSpaceC (I := I) (x := x) :=
by
  classical
  refine
    { toFun := fun t => acs.Jc₁ (I := I) (M := M) x t
      map_add' := by
        intro u v
        simp [Jc₁]
      map_smul' := ?_ }
  intro c t
  refine TensorProduct.induction_on t ?h0 ?htmul ?hadd
  · simp [Jc₁]
  · intro z v
    simp [AlmostComplexStructure.Jc₁, TensorProduct.smul_tmul']
  · intro t₁ t₂ ih₁ ih₂
    simp [map_add, ih₁, ih₂]

-- Prove that Jc^2 = -Id on the complexified tangent space
theorem Jc_sq (acs : AlmostComplexStructure (I := I) (M := M)) (x : M) :
    (acs.Jc (I := I) (M := M) x).comp (acs.Jc (I := I) (M := M) x)
      = - (LinearMap.id :
          TangentSpaceC (I := I) (x := x) →ₗ[ℂ] TangentSpaceC (I := I) (x := x)) := by
  classical
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?h0 ?htmul ?hadd
  · simp
  · intro z v
    have hv : acs.J x (acs.J x v) = -v := by
      have h := congrArg (fun f => f v) (acs.J_sq x)
      simpa [LinearMap.comp_apply, LinearMap.id_apply] using h
    simp [AlmostComplexStructure.Jc, AlmostComplexStructure.Jc₁,
      LinearMap.comp_apply, hv, TensorProduct.tmul_neg]
  · intro t₁ t₂ ih₁ ih₂
    simp [map_add, ih₁, ih₂]



-- Define the (1,0) and (0,1) subspaces of the complexified tangent space
def T01 (acs : AlmostComplexStructure (I := I) (M := M)) (x : M) :
    Submodule ℂ (TangentSpaceC (I := I) (x := x)) :=
  Module.End.eigenspace (acs.Jc x) (-Complex.I)

def T10 (acs : AlmostComplexStructure (I := I) (M := M)) (x : M) :
    Submodule ℂ (TangentSpaceC (I := I) (x := x)) :=
  Module.End.eigenspace (acs.Jc x) (Complex.I)

end AlmostComplexStructure
end

end Manifold

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Short exactness from a distinguished triangle of the specified single objects

The connecting map and distinguished triangle are actual derived data.
The maps on degree-zero homology are identified with the original maps.
-/

@[expose] public noncomputable section
universe w v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A distinguished triangle on the specified single objects and original
maps gives a short exact sequence in the original abelian category. -/
theorem shortExact_of_distinguished_single_triangle
    (S : ShortComplex C)
    (δ : (DerivedCategory.singleFunctor C 0).obj S.X₃ ⟶
      ((DerivedCategory.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((DerivedCategory.singleFunctor C 0).map S.f)
      ((DerivedCategory.singleFunctor C 0).map S.g) δ ∈ distTriang (DerivedCategory C)) :
    S.ShortExact := by
  let F := DerivedCategory.singleFunctor C 0
  let H := DerivedCategory.homologyFunctor C 0
  let G := F ⋙ H
  let T := Triangle.mk (F.map S.f) (F.map S.g) δ
  have hT' : T ∈ distTriang (DerivedCategory C) := hT
  have hm : Mono (G.map S.f) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT' (-1) 0 rfl).mpr
    exact (DerivedCategory.isZero_of_isGE (F.obj S.X₃) 0 (-1) (by decide)).eq_of_src _ _
  have hn : Epi (G.map S.g) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT' 0 1 rfl).mpr
    exact (DerivedCategory.isZero_of_isLE (F.obj S.X₁) 0 1 (by decide)).eq_of_tgt _ _
  have he : (S.map G).Exact := DerivedCategory.HomologySequence.exact₂ T hT' 0
  have hshort : (S.map G).ShortExact := ShortComplex.ShortExact.mk' he hm hn
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0)) hshort

end SerrePositivity

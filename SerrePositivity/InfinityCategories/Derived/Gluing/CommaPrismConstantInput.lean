module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismUnitEdge
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismReindex
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero

/-! 元 augmentation prism の定値入力を、同じ閉 augmentation 辺の全引き戻しとして回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgGluingSimplex_constant_one_unit (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (x : E) :
    InfinityCategories.PinchedHom.constant (X := dgNerve R E) (Simplex.vertex x) 1 =
      Simplex.ofEdge (fun _ : Fin 2 => x) (unitElement R x) :=
  (pinchedConstant_one (X := dgNerve R E) (Simplex.vertex x)).trans
    (dgCommaNerve_vertex_identity_simplex R E x)

lemma dgGluingSimplex_unit_pullback (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] (x : E) {n : ℕ} (β : Fin (n + 1) →o Fin 2) :
    (Simplex.ofEdge (fun _ : Fin 2 => x) (unitElement R x)).pullback β =
      InfinityCategories.PinchedHom.constant (X := dgNerve R E) (Simplex.vertex x) n := by
  rw [← dgGluingSimplex_constant_one_unit R E x]
  exact InfinityCategories.PinchedHom.constant_pullback (X := dgNerve R E) (Simplex.vertex x)
    (SimplexCategory.mkHom β)

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingCommaPrism_constant_input (X : DGFunctorCommaObject R C E F)
    {n : ℕ} (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R C E F
      (InfinityCategories.PinchedHom.constant
        (X := dgNerve R (DGFunctorCommaObject R C E F)) (Simplex.vertex X) n) β =
      (dgClosedEdge R E X.augmentation).edge.pullback β := by
  have h := dgCommaAugmentationPrismSimplex_pullback R C E F
    (Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)) β OrderHom.id
  rw [dgGluingSimplex_unit_pullback R _ X β, OrderHom.id_comp,
    dgGluingCommaPrism_unitEdge R C E F X] at h
  exact h

end SerrePositivity.InfinityCategories

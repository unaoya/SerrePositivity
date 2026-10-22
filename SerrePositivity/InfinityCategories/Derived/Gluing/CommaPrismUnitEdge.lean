module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugActualComponent
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges

/-! 対象宇宙を固定せず、実 augmentation prism の単位入力辺を元の閉辺へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingSimplex_unit_map (X : C) :
    (Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)).map F =
      Simplex.ofEdge (fun _ : Fin 2 => F.obj X) (unitElement R (F.obj X)) := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  change (F.map X X).f 0 (unitElement R X).val = (unitElement R (F.obj X)).val
  exact DGFunctor.map_unitElement R F X

lemma dgGluingCommaPrism_unitEdge (X : DGFunctorCommaObject R C E F) :
    dgCommaAugmentationPrismSimplex R C E F
      (Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)) OrderHom.id =
    (dgClosedEdge R E X.augmentation).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgCommaAugmentationPrismSimplex_unitEdge R C E F X)

end SerrePositivity.InfinityCategories

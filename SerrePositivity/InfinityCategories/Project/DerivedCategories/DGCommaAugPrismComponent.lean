module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugNervePrism
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LowDimensional
/-!
概要：実 augmentation prism の同じ単位辺を評価し、元の augmentation 成分を回収する。
方針：二点の切断補正が零となる式と、実 dg 関手の単位保存・右単位律を使う。
規約：辺の係数そのものの照合。使われ方：実 augmentation の頂点成分の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 実単体族の単位入力辺での係数は、元の同じ augmentation。 -/
lemma dgCommaAugmentationPrismSimplex_unitEdge :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)) (OrderHom.id)).edgeHom
        0 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F X).val := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R C E F s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_two R C E F s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs : s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement R X).val := rfl
  rw [hs] at hm
  change _ = _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement) (y := X.replacement)
    (z := F.obj X.source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F X).val
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map X X).f 0 (unitElement R X).val)
    (add_zero 0) at hm
  rw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement] at hm
  have hu := _root_.SerrePositivity.DifferentialGraded.compose_unit R (D := E)
    (x := X.replacement) (y := F.obj X.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F X).val
  exact he.trans (heq_of_eq (hm.trans hu))
/-- 実 nerve prism の単位入力辺でも、同じ実 augmentation を回収する。 -/
lemma dgCommaAugmentationNervePrism_unitEdge :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNervePrism R C E F).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X),
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u (max v w)})))).edgeHom
          0 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F X).val := by
  change HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)) OrderHom.id).edgeHom
      0 1 (by decide)) _
  exact dgCommaAugmentationPrismSimplex_unitEdge R C E F X
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationNervePrism
public import SerrePositivity.InfinityCategories.DGNerve.LowDimensional
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X : DGModuleFunctorResolutionObject R C E F)
/-- 実単体族の単位入力辺での係数は、元の同じ augmentation。 -/
lemma dgModuleAugmentationPrismSimplex_unitEdge :
    HEq ((dgModuleAugmentationPrismSimplex R C E F
      (Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)) (OrderHom.id)).edgeHom
        0 1 (by decide))
      (dgModuleAugmentationComponent R C E F X).val := by
  let s := Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)
  have he := dgModuleAugmentationPrismData_hom_mixed R C E F s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl)
  have hm := dgModuleAugmentationPrismMixedHom_two R C E F s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs : s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) =
      (unitElement R X).val := rfl
  rw [hs] at hm
  change _ = compose R (x := X.replacement.val) (y := X.replacement.val)
    (z := F.obj X.source) (dgModuleAugmentationComponent R C E F X).val
    (((dgModuleAugmentationSource R C E F).map X X).f 0 (unitElement R X).val)
    (add_zero 0) at hm
  rw [DGFunctor.map_unitElement] at hm
  have hu := compose_unit R (D := RightModule R E)
    (x := X.replacement.val) (y := F.obj X.source)
    (dgModuleAugmentationComponent R C E F X).val
  exact he.trans (heq_of_eq (hm.trans hu))
/-- 実 nerve prism の単位入力辺でも、同じ実 augmentation を回収する。 -/
lemma dgModuleAugmentationNervePrism_unitEdge :
    HEq (((dgModuleAugmentationNervePrism R C E F).app (Opposite.op ⦋1⦌)
      (Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X),
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max v (max (u + 1) w)})))).edgeHom
          0 1 (by decide))
      (dgModuleAugmentationComponent R C E F X).val := by
  change HEq ((dgModuleAugmentationPrismSimplex R C E F
    (Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X)) OrderHom.id).edgeHom
      0 1 (by decide)) _
  exact dgModuleAugmentationPrismSimplex_unitEdge R C E F X
end SerrePositivity.InfinityCategories

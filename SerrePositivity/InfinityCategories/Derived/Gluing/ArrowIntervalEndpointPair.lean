module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionEndpointPair
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalMappingProductIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowEndpointPair
/-!
概要：矢印 Hom の二端評価を積の区間 Hom から元の二可変辺へ厳密に分離する。
方針：全区間族を展開し、両端評価の二射影を比較する。
規約：元の四頂点と元の端点輸送を省略しない。
使われ方：正本標的の区間引き戻しを二入力付き合成座標へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowEndpointPair_vertex :
    (F2.arrowEndpointPair X).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm f.edge)) = (a, b) :=
  Prod.ext (dgGluingArrowEdgeEvaluation_zero f) (dgGluingArrowEdgeEvaluation_one f)

def dgGluingArrowIntervalEndpointPair :=
  intervalMappingPostOfEq (F2.arrowEndpointPair X)
    (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge))
    (dgGluingArrowEndpointPair_vertex f) (dgGluingArrowEndpointPair_vertex g) ≫
      dgGluingIntervalProductSplit a c b d

lemma dgGluingArrowIntervalEndpointPair_components :
    dgGluingArrowIntervalEndpointPair f g =
      lift (dgGluingArrowHomSourceComponent f g (𝟙 _))
        (dgGluingArrowHomTargetComponent f g (𝟙 _)) := by
  have hp := intervalMappingPostOfEq_uncurry (F2.arrowEndpointPair X)
    (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge))
    (dgGluingArrowEndpointPair_vertex f) (dgGluingArrowEndpointPair_vertex g) (𝟙 _)
  simp only [Category.id_comp] at hp
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingArrowIntervalEndpointPair, dgGluingIntervalProductSplit,
      Category.assoc, lift_fst]
    apply intervalMappingUncurry_injective a c
    have hs := intervalMappingPostOfEq_uncurry
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge))
      (dgGluingArrowEdgeEvaluation_zero f) (dgGluingArrowEdgeEvaluation_zero g) (𝟙 _)
    simp only [Category.id_comp] at hs
    rw [intervalMappingPost_uncurry, hp, dgGluingArrowHomSourceComponent,
      Category.id_comp, hs]
    rfl
  · simp only [dgGluingArrowIntervalEndpointPair, dgGluingIntervalProductSplit,
      Category.assoc, lift_snd]
    apply intervalMappingUncurry_injective b d
    have hs := intervalMappingPostOfEq_uncurry
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (functorVertex (SSet.yonedaEquiv.symm f.edge))
      (functorVertex (SSet.yonedaEquiv.symm g.edge))
      (dgGluingArrowEdgeEvaluation_one f) (dgGluingArrowEdgeEvaluation_one g) (𝟙 _)
    simp only [Category.id_comp] at hs
    rw [intervalMappingPost_uncurry, hp, dgGluingArrowHomTargetComponent,
      Category.id_comp, hs]
    rfl
end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveFunctor
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveFiber
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveLeftFibration
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison

/-!
概要：係数の対象ごとの同値から weighted nerve の全空間の前合成同値を得る。
方針：fiber と係数の同型の自然性を証明し、left fibration の fiber ごとの判定へ適用する。
規約：同じ通常の底の圏と Kan な係数の図式を使う。
使われ方：Kerodon Corollary 5.6.0.6、自然な edgewise 反転比較を weighted nerve の比較にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：weighted nerve の fiber の標準同型は係数の自然変換について自然。
方針：一定の底の上の重み付き図式の各成分と、後合成された Yoneda 単体を比較する。
規約：図式の値の Kan 性はこの等式には不要。
使われ方：Kerodon §5.3.3、fiber の比較を係数の成分の比較へ戻す。 -/
lemma weightedNerveMap_fiber_naturality {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (c : C) :
    weightedNerveFiberMap F c ≫ vertexFiberMap (weightedNerveProjection F)
      (weightedNerveProjection G) (weightedNerveMap η) (weightedNerveMap_projection η) (nerveVertex c) =
      η.app c ≫ weightedNerveFiberMap G c := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change (stdSimplex.map (simplexPrefixInclusion i.val n _) ≫ SSet.yonedaEquiv.symm s) ≫ η.app c =
    stdSimplex.map (simplexPrefixInclusion i.val n _) ≫ SSet.yonedaEquiv.symm ((η.app c).app _ s)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- 概要：Kan な係数図式の自然変換が各対象で圏同値なら weighted nerve の射は前合成同値。
方針：係数と fiber の同型による自然性から fiber ごとの同値を得て、全空間の判定を使う。
規約：前合成同値は全ての quasicategory への関手の比較としての性質。
使われ方：Kerodon Corollary 5.6.0.6、反転した係数と元の係数の全空間の比較。 -/
lemma weightedNerveMap_isPrecompositionEquivalence {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (h : ∀ c, IsQCatEquivalence (η.app c)) :
    IsPrecompositionEquivalence (weightedNerveMap η) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    (weightedNerveProjection F) (weightedNerveProjection G) (weightedNerveMap η)
    (weightedNerveMap_projection η)
  intro b
  obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective b
  apply (qCatEquivalenceOfIso (weightedNerveFiberIso F c)).isQCatEquivalence.cancel_left
  change IsQCatEquivalence (weightedNerveFiberMap F c ≫ vertexFiberMap
    (weightedNerveProjection F) (weightedNerveProjection G) (weightedNerveMap η)
      (weightedNerveMap_projection η) (nerveVertex c))
  rw [weightedNerveMap_fiber_naturality]
  exact (h c).comp (qCatEquivalenceOfIso (weightedNerveFiberIso G c)).isQCatEquivalence

end SerrePositivity.InfinityCategories

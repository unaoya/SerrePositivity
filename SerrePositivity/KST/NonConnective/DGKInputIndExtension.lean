module
public import SerrePositivity.KST.NonConnective.DGKInputIndNativeFamily

/-!
概要：固定 ν の Ind 延長を、同じ Yoneda 制限の充満忠実性で一意比較する。
方針：公開制限同値の実逆を各関手に適用し、保存関手の全写像空間から比較を反映する。
規約：固定した元の Indω・Yoneda・制限同値を保持する。D-8 の実 cone との同一視はしない。
使われ方：K-7 d4 の Ind 作用の合成比較と Morita 同値の延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

local instance indExtensionRegular : Fact (Cardinal.aleph0.{w}).IsRegular :=
  Cardinal.fact_isRegular_aleph0
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 元の制限同値の逆が選んだ、指定関手の保存延長の同じ頂点。 -/
def dgKInputIndExtensionContinuousVertex
    (f : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj ⟶ dgKInputIndCompletion R B) :=
  (dgKInputIndRestrictionEquivalence R A B).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)

/-- 固定 ν の指定関手を、元の同じ Indω 上の実関手へ延長する。 -/
def dgKInputIndExtension
    (f : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj ⟶ dgKInputIndCompletion R B) :
    dgKInputIndCompletion R A ⟶ dgKInputIndCompletion R B :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (dgKInputIndExtensionContinuousVertex R A B f).val

/-- 元の実延長は同じ小さい filtered native 余極限を保存する。 -/
theorem dgKInputIndExtension_preservesFilteredColimits
    (f : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj ⟶ dgKInputIndCompletion R B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 (dgKInputIndExtension R A B f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (dgKInputIndExtensionContinuousVertex R A B f)

/-- 同じ指定延長の元の Yoneda 制限は、元の指定関手を全関手同型で回収する。 -/
def dgKInputIndExtension_restrictionIso
    (f : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj ⟶ dgKInputIndCompletion R B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫
      dgKInputIndExtension R A B f) f := by
  have e := (dgKInputIndRestrictionEquivalence R A B).invHomIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj)).app _).app
      (Opposite.op ⦋0⦌) (dgKInputIndExtensionContinuousVertex R A B f).val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) at e
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKInputIndExtension R A B f) =
      (dgKInputIndExtensionContinuousVertex R A B f).val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  rw [← hv] at e
  exact e

/-- 概要：固定 ν の同じ Indω の保存関手は、元の Yoneda 上の比較から全関手で比較できる。
方針：I-2 の元の制限射の充満忠実性で指定頂点同型を反映し、同じ全部分包含へ送る。
規約：F・G の保存性と指定比較だけを入力とする。新しい逆射選択は導入しない。
使われ方：d4 の Ind 作用の恒等・合成・選択比較。
-/
def dgKInputIndFunctorIso_of_restriction
    (F G : dgKInputIndCompletion R A ⟶ dgKInputIndCompletion R B)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj ≫ G)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := by
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.kappaContinuousFunctorVertex Cardinal.aleph0 F hF
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.kappaContinuousFunctorVertex Cardinal.aleph0 G hG
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction Cardinal.aleph0 (dgKInputStableValue R A).obj
        (dgKInputIndCompletion R B)).app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction Cardinal.aleph0 (dgKInputStableValue R A).obj
        (dgKInputIndCompletion R B)).app (Opposite.op ⦋0⦌) y) := e
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestriction_isFullyFaithful Cardinal.aleph0
      (dgKInputStableValue R A).obj (dgKInputIndCompletion R B)).preimageVertexIso e')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.kappaContinuousFunctorInclusion Cardinal.aleph0
      (dgKInputIndCompletion R A) (dgKInputIndCompletion R B))

end SerrePositivity.KST.NonConnective

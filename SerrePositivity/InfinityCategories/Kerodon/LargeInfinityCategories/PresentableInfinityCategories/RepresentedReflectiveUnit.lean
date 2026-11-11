module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentedRestrictionInversion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointFiberEvaluation

/-!
概要：反映から得た表現対象の全 Hom は元の反映単位を反転する。
方針：反映で写した単位の全可逆性を評価し、同じ実辺の反対像へ移す。
規約：元の単位成分を表す辺を指定して保持する。
使われ方：表現対象の局所性を写像空間の前合成で検査する直前の界面。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の反映単位の各点の像は reflector によって可逆になる。
方針：全単位の後合成の可逆性を同じ頂点で評価し、評価と後合成の可換性を使う。
規約：任意の同型な比較に単位成分を置き換えない。
使われ方：指定単位を表す実辺の反転性。 -/
lemma reflectiveUnit_map_isIso {X : SSet.{u}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) (x : X _⦋0⦌) :
    IsIso ((hoFunctor.map r.reflector).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x)) := by
  have : IsIso ((hoFunctor.map ((ihom X).map r.reflector)).toFunctor.map r.unit) :=
    r.adjunction.unit_postcompLeft_isIso
  have he : IsIso ((hoFunctor.map ((ihom X).map r.reflector ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)).toFunctor.map r.unit) := by
    rw [CategoryTheory.Functor.map_comp]
    rw [Cat.Hom.comp_map]
    infer_instance
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.evaluateFunctorAt_post] at he
  have : IsIso ((hoFunctor.map r.reflector).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map r.unit)) := by
    rw [CategoryTheory.Functor.map_comp] at he
    exact he
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
  simp only [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：反映へ引き戻した前層の全表現可能 Hom は元の単位の反対辺を反転する。
方針：指定単位の reflector による像の可逆性を、表現された制限前層へ移す。
規約：元の単位成分との一致を明示し、局所性を追加入力にしない。
使われ方：局所対象の前合成判定による表現対象の下降。 -/
lemma representedReflectiveUnit_inverts_op_edge
    {X : SSet.{u + 1}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u + 1}).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (z : X _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map r.reflector ≫ F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram))
    (x : X _⦋0⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) x (r.localization.app _ x))
    (he : Truncated.HomotopyCategory.homMk e = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.representedRestriction_inverts_op_edge r.reflector F z h e
  change IsIso ((hoFunctor.map r.reflector).toFunctor.map
    (Truncated.HomotopyCategory.homMk e))
  rw [he]
  exact reflectiveUnit_map_isIso r x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

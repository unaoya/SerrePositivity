module
public import SerrePositivity.KST.Fibration.Relative.ClosedStableFlags
public import SerrePositivity.KST.SConstruction.SingleRealizationEquivalence
public import SerrePositivity.KST.Fibration.RelativePullbackMulti

/-!
概要：P に cofiber を持つ実辺への相対 cofiber 射影。
方針：元の全 cofiber 射影を正確な頂点逆像に制限し、trivial Kan 性を使う。
規約：商・Verdier 列・完備化の仮定なし。使われ方：閉じた部分圏版の相対加法性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の全 W 辺と全自然変換。方針：cofiber 条件の全部分圏。
規約：W は cofiber が P。使われ方：相対射影の標的。 -/
def closedArrowModel {B : StableModel.{u}} (P : ClosedStablePredicate B) : StableModel.{u} :=
  closedStableModel (closedArrowPredicate P)

/-- 概要：全 cofiber 射影は P 条件を正確に反映。
方針：同じ実四角形の底辺と cofiber を照合する。
規約：選択による対象の変更なし。使われ方：元の境界持ち上げの制限。 -/
lemma closedCofiberProjection_predicate {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (v : (cofiberDiagrams B.carrier) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top B) P).predicate v ↔
      (closedArrowPredicate P).predicate ((cofiberProjection B.carrier).app _ v) := by
  let s := vertexCofiberSquare (B := flagAmbient B) v
  have hv := cofiberProjection_vertex_simplex (flagAmbient B) v
  change arrowVertexSimplex ((cofiberProjection B.carrier).app (Opposite.op ⦋0⦌) v) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).edge at hv
  have hc : (cofiberStableQuotient B).val.app (Opposite.op ⦋0⦌) v = s.cofiber :=
    cofiberVertex_corner (flagAmbient B) v
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)
  have hp : (relativeCofiberPredicate (ClosedStablePredicate.top B) P).predicate v ↔
      P.predicate s.cofiber := by
    change (True ∧ P.predicate ((cofiberStableQuotient B).val.app _ v)) ↔ _
    simpa only [true_and] using (congrArg P.predicate hc).to_iff
  have ha := closedArrowPredicate_iff P ((cofiberProjection B.carrier).app _ v)
  have hs : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).edge ∈ closedStableEdges P ↔
      P.predicate s.cofiber := closedStableEdges_iff_cofiber (B := B) P s
  exact hp.trans (hs.symm.trans (((congrArg (· ∈ closedStableEdges P) hv).to_iff).symm.trans
    ha.symm))

/-- 概要：全相対 cofiber 補完から元の W 底辺への射影。
方針：正確な逆像の全部分圏へ制限。規約：全高次族を保持。
使われ方：閉じた部分圏版の一段加法性。 -/
def closedCofiberProjection {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (relativeCofiberStableModel (ClosedStablePredicate.top B) P).carrier ⟶
      (closedArrowModel P).carrier :=
  fullPredicateMap (cofiberProjection B.carrier)
    (relativeCofiberPredicate (ClosedStablePredicate.top B) P).predicate
    (closedArrowPredicate P).predicate (fun v => (closedCofiberProjection_predicate P v).1)

/-- 概要：同じ射影の全境界持ち上げ。方針：正確な逆像制限の既存定理。
規約：追加 instance 仮定なし。使われ方：全 cofiber 選択を保つ比較。 -/
instance closedCofiberProjection_trivialKanFibration {B : StableModel.{u}}
    (P : ClosedStablePredicate B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (closedCofiberProjection P) :=
  fullPredicateMap_trivialKanFibration _ _ _ (closedCofiberProjection_predicate P)

/-- 概要：相対 cofiber と元の W 辺の完全な同値。
方針：同じ trivial Kan 射影の既存の coherent 逆を使う。
規約：順射は元の射影。使われ方：K-S• 加法性への接続。 -/
def closedArrowCofiberEquivalence {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    StableModelEquivalence (relativeCofiberStableModel (ClosedStablePredicate.top B) P)
      (closedArrowModel P) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (closedCofiberProjection P)
  exact {
    hom := ⟨e.hom, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence).preservesZero,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence).preservesCofiber⟩
    inv := ⟨e.inv, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence).preservesZero,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence).preservesCofiber⟩
    homInvIso := e.homInvIso
    invHomIso := e.invHomIso }

/-- 概要：元の W 底辺への比較は単回実現で局所化同型。
方針：同じ実完全同値への既存の S• 定理。
規約：相対加法性以外の不変性なし。使われ方：任意旗への基底変換。 -/
theorem closedCofiberProjection_realization_isIso {B : StableModel.{u}}
    (P : ClosedStablePredicate B) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (coreSRealizationFunctor.map (closedArrowCofiberEquivalence P).hom)) :=
  coreSRealization_map_localized_isIso_of_equivalence (closedArrowCofiberEquivalence P)

end SerrePositivity.KST.Fibration.Relative

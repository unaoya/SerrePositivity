module
public import SerrePositivity.KST.Fibration.Relative.ClosedTailFlags
public import SerrePositivity.KST.Fibration.FullPredicatePullback
public import SerrePositivity.KST.Fibration.ClosedTopIso

/-!
概要：閉じた条件 P の元の有限旗に対する共有端点引き戻し。
方針：標準 tail の押し出しを全図式圏に移し、全頂点条件で制限する。
規約：商の核条件を使わない。使われ方：相対加法性の基底変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の旗を tail に制限する射。
方針：正確な全頂点条件の逆像制限。規約：全単体を保持。
使われ方：有限旗と貼り合わせの比較。 -/
def closedFlagTailRestriction {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    (closedFlagModel P ⦋n + 2⦌).carrier ⟶ (closedTailModel P n).carrier :=
  fullPredicateMap ((pre (standardTailInclusion n)).app B.carrier)
    (closedFlagStablePredicate P ⦋n + 2⦌).predicate (closedTailPredicate P n).predicate
    (fun v => (closedFlag_tail_iff P n v).1)

/-- 概要：制限は全境界を持ち上げる。
方針：inner anodyne 制限と全部分圏の逆像補題。
規約：追加モデル構造なし。使われ方：実現比較。 -/
instance closedFlagTailRestriction_trivialKanFibration {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (closedFlagTailRestriction P n) := by
  have := standardTailInclusion_pre_trivialKanFibration n B.carrier
  exact fullPredicateMap_trivialKanFibration _ _ _ (closedFlag_tail_iff P n)

/-- 概要：最後の辺の元の始点を一点図式として取る。
方針：周囲の図式制限に包含を前合成。
規約：選択した cofiber への置換なし。使われ方：共有端点。 -/
def closedArrowSourceDiagram {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedArrowModel P ⟶ ambientDiagramModel (Δ[0] : SSet.{u}) (flagAmbient B) :=
  closedStableInclusion (closedArrowPredicate P) ≫
    ambientDiagramRestriction (flagAmbient B) (stdSimplex.δ (1 : Fin 2))

/-- 概要：先行旗の元の終点を一点図式として取る。
方針：共有端点への周囲制限。規約：元の射を保持。
使われ方：有限旗の実引き戻し。 -/
def closedTailEndpointDiagram {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    closedFlagModel P ⦋n + 1⦌ ⟶ ambientDiagramModel (Δ[0] : SSet.{u}) (flagAmbient B) :=
  closedStableInclusion (closedFlagStablePredicate P ⦋n + 1⦌) ≫
    ambientDiagramRestriction (flagAmbient B) (standardTailEndpoint n)

/-- 概要：元の一点図式上での実引き戻し。
方針：同じ標準押し出しを全部分図式に制限。
規約：局所化前の SSet 図式。使われ方：相対 cofiber 補完との貼り合わせ。 -/
theorem closedTail_isPullback {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    IsPullback (closedTailPrefix P n).val (closedTailEdge P n).val
      (closedTailEndpointDiagram P n).val (closedArrowSourceDiagram P).val := by
  exact isPullback_fullPredicates
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (standardTail_isPushout n) B.carrier)
    (closedTailPredicate P n).predicate (closedFlagStablePredicate P ⦋n + 1⦌).predicate
    (closedArrowPredicate P).predicate (fun _ => Iff.rfl)

/-- 概要：相対 subobject の値域と一致する元の端点射。
方針：一点図式の同型と全頂点の同型を使用。
規約：P の拡大なし。使われ方：相対加法性の底。 -/
def closedTailEndpoint {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ) :
    closedFlagModel P ⦋n + 1⦌ ⟶ closedStableModel (ClosedStablePredicate.top B) :=
  closedTailEndpointDiagram P n ≫ (ambientPointExactIso (flagAmbient B)).hom ≫ closedTopLift B

/-- 概要：元の辺の始点を全頂点部分圏値で保持。
方針：同じ一点図式の評価同型。規約：cofiber の変更なし。
使われ方：相対 subobject との照合。 -/
def closedArrowSource {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedArrowModel P ⟶ closedStableModel (ClosedStablePredicate.top B) :=
  closedArrowSourceDiagram P ≫ (ambientPointExactIso (flagAmbient B)).hom ≫ closedTopLift B

/-- 概要：共有端点の値域を変えた同じ実引き戻し。
方針：元の引き戻しを指定同型で運ぶ。
規約：SSet 値の四角形。使われ方：相対 cofiber 基底変換。 -/
theorem closedTail_top_isPullback {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    IsPullback (closedTailPrefix P n).val (closedTailEdge P n).val
      (closedTailEndpoint P n).val (closedArrowSource P).val := by
  let e := stableModelForget.mapIso
    (ambientPointExactIso (flagAmbient B) ≪≫ (closedTopExactIso B).symm)
  exact (closedTail_isPullback P n).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) rfl rfl

end SerrePositivity.KST.Fibration.Relative

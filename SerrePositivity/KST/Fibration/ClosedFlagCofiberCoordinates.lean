module
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagFunctor
public import SerrePositivity.KST.Fibration.Relative.ClosedCofiberProjection
public import SerrePositivity.KST.SConstruction.MultiRealization

/-!
概要：任意の閉じた安定部分圏 P に対する全有限旗の共通 cofiber 座標。
方針：全合成辺の完全制限へ元の相対 cofiber 射影の同じ切断を合成する。
規約：商・Verdier 列・retract 閉包を使わず、全再添字で同じ補完を保持する。
使われ方：K-B2 向け有限旗比較の共通帰納に渡す実座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative

/-- 概要：元の全旗の指定合成辺を P cofiber を持つ辺として抽出する。
方針：全辺に課された閉条件の同じ成分へ制限する。
規約：全自然変換を保持。使われ方：共通 cofiber 補完の実入力。 -/
def closedFlagEdge {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : closedFlagModel P n ⟶ closedArrowModel P :=
  closedStableMap (closedFlagStablePredicate P n) (closedArrowPredicate P)
    (diagramRestrictionMap (flagAmbient B) α) (fun v hv => hv α)

/-- 概要：辺抽出後の包含は元の実前合成。
方針：同じ完全な全部分圏制限の回収公式。
規約：厳密等式。使われ方：全再添字の照合。 -/
theorem closedFlagEdge_inclusion {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    closedFlagEdge P α ≫ closedStableInclusion (closedArrowPredicate P) =
      closedStableInclusion (closedFlagStablePredicate P n) ≫
        diagramRestrictionMap (flagAmbient B) α :=
  closedStableMap_inclusion _ _ _ _

/-- 概要：元の辺抽出は全ての面・退化・合成辺の制限と厳密に可換。
方針：元の周囲への包含で前合成の結合則を使う。
規約：同じ合成辺。使われ方：全有限旗座標の自然性。 -/
theorem closedFlagEdge_reindex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    closedFlagMap P θ ≫ closedFlagEdge P α = closedFlagEdge P (α ≫ θ) := by
  apply closedStableInclusion_cancel (closedArrowPredicate P)
  rw [Category.assoc, closedFlagEdge_inclusion, ← Category.assoc,
    closedFlagMap_inclusion, Category.assoc, closedFlagEdge_inclusion]
  apply Subtype.ext
  change _ ≫ ((pre (stdSimplex.map θ)).app B.carrier ≫
    (pre (stdSimplex.map α)).app B.carrier) =
      _ ≫ (pre (stdSimplex.map (α ≫ θ))).app B.carrier
  rw [stdSimplex.map_comp, pre_map, NatTrans.comp_app]

/-- 概要：同じ全相対 cofiber 補完の逆は元の底辺を厳密に回収する。
方針：元の trivial Kan 射影の同じ切断を使う。
規約：別の逆を選ばない。使われ方：全旗の共通補完。 -/
theorem closedArrowCofiberEquivalence_section {B : StableModel.{u}}
    (P : ClosedStablePredicate B) :
    (closedArrowCofiberEquivalence P).inv ≫ (closedArrowCofiberEquivalence P).hom =
      𝟙 (closedArrowModel P) := by
  apply Subtype.ext
  exact Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (closedCofiberProjection P))

/-- 概要：全旗の指定合成辺に同じ相対 cofiber 補完を付ける。
方針：元の辺抽出と同じ切断を合成する。
規約：全再添字で一つの切断。使われ方：P 値 cofiber の実完全射。 -/
def closedFlagCofiberCompletion {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    closedFlagModel P n ⟶ relativeCofiberStableModel (ClosedStablePredicate.top B) P :=
  closedFlagEdge P α ≫ (closedArrowCofiberEquivalence P).inv

/-- 概要：同じ補完の底辺は元の実合成辺そのもの。
方針：共通切断の厳密回収を代入する。
規約：同型による置換なし。使われ方：加法性成分の照合。 -/
theorem closedFlagCofiberCompletion_projection {B : StableModel.{u}}
    (P : ClosedStablePredicate B) {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    closedFlagCofiberCompletion P α ≫ (closedArrowCofiberEquivalence P).hom =
      closedFlagEdge P α := by
  rw [closedFlagCofiberCompletion, Category.assoc, closedArrowCofiberEquivalence_section,
    Category.comp_id]

/-- 概要：元の全旗の指定合成辺の P 値 cofiber。
方針：同じ補完から実 quotient 頂点を読む。
規約：実 cofiber 射影であり Verdier 商ではない。
使われ方：有限積に束ねる共通 cofiber 座標。 -/
def closedFlagCofiber {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) : closedFlagModel P n ⟶ closedStableModel P :=
  closedFlagCofiberCompletion P α ≫ relativeCofiberQuotient (ClosedStablePredicate.top B) P

/-- 概要：同じ P 値 cofiber は全単体作用素と厳密に可換。
方針：共通切断と商頂点を保ち、元の辺抽出の再添字を使う。
規約：合成辺と退化辺を含む。使われ方：有限旗の全自然性。 -/
theorem closedFlagCofiber_reindex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) :
    closedFlagMap P θ ≫ closedFlagCofiber P α = closedFlagCofiber P (α ≫ θ) := by
  simp only [closedFlagCofiber, closedFlagCofiberCompletion, ← Category.assoc,
    closedFlagEdge_reindex]

end SerrePositivity.KST.Fibration

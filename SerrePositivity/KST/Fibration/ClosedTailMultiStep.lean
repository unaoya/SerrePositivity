module
public import SerrePositivity.KST.Fibration.StableTrivialPullbackSection
public import SerrePositivity.KST.Fibration.ClosedFlagCofiberCoordinates
public import SerrePositivity.KST.Fibration.Relative.ClosedTailAdditivity

/-!
概要：P 相対旗の元の先行旗と最後の cofiber の全正反復比較。
方針：同じ指定補完切断で相対加法性を引き戻し、元の二成分を厳密に回収する。
規約：核表示や商を使わず、K-B2 の元の相対加法性を消費する。
使われ方：有限旗の共通帰納への実同値入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ)

/-- 概要：同じ最後の辺に元の共通 cofiber 補完を付ける切断。
方針：元の指定切断を保つ共通基底変換構成。
規約：選択の変更なし。使われ方：相対加法性と同じ有限旗座標の照合。 -/
def closedTailCompletionSection : closedTailModel P n ⟶ closedTailCompletion P n :=
  stableTrivialPullbackSection (closedCofiberProjectionExact P)
    (closedArrowCofiberEquivalence P).inv (closedArrowCofiberEquivalence_section P)
    (closedTailEdge P n)

/-- 概要：最後の辺の同じ P 値 cofiber。
方針：同じ共通切断と quotient 頂点を合成する。
規約：Verdier 商なし。使われ方：実比較段の第二成分。 -/
def closedTailCofiber : closedTailModel P n ⟶ closedStableModel P :=
  closedTailEdge P n ≫ (closedArrowCofiberEquivalence P).inv ≫
    relativeCofiberQuotient (ClosedStablePredicate.top B) P

/-- 概要：元の先行旗と同じ最後の cofiber の実反復比較。
方針：二つの元の実完全射の実現を束ねる。
規約：全反復で同じ座標。使われ方：元の全有限旗からの帰納比較。 -/
def closedTailMultiStep (r : ℕ) : (multiRealizationFunctor r).obj (closedTailModel P n) ⟶
    (multiRealizationFunctor r).obj (closedFlagModel P ⦋n + 1⦌) ⊗
      (multiRealizationFunctor r).obj (closedStableModel P) :=
  lift ((multiRealizationFunctor r).map (closedTailPrefix P n))
    ((multiRealizationFunctor r).map (closedTailCofiber P n))

/-- 概要：同じ補完切断を通る相対加法性は元の二成分の実比較そのもの。
方針：共通基底変換切断の両射影の厳密回収を使う。
規約：元の cofiber 選択を保持。使われ方：実加法性の局所化同型を渡す。 -/
theorem closedTailCompletionSection_pair (F : StableModel.{u} ⥤ SSet.{u}) :
    F.map (closedTailCompletionSection P n) ≫ (closedTailRelativePullback P n).pair F =
      lift (F.map (closedTailPrefix P n)) (F.map (closedTailCofiber P n)) := by
  unfold RelativePullback.pair
  rw [comp_lift, ← F.map_comp, ← F.map_comp]
  apply congrArg₂ lift
  · change F.map (closedTailCompletionSection P n ≫
      (stableTrivialPullbackSnd (closedCofiberProjectionExact P) (closedTailEdge P n) ≫
        closedTailPrefix P n)) = _
    rw [← Category.assoc, closedTailCompletionSection, stableTrivialPullbackSection_snd,
      Category.id_comp]
  · change F.map (closedTailCompletionSection P n ≫
      (stableTrivialPullbackFst (closedCofiberProjectionExact P) (closedTailEdge P n) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top B) P)) = _
    rw [← Category.assoc, closedTailCompletionSection, stableTrivialPullbackSection_fst]
    rfl

/-- 概要：元の先行旗と最後の P 値 cofiber の比較は全正反復で局所化同型。
方針：同じ補完切断の実同値と K-B2 の相対加法性を合成する。
規約：B と P 以外の存在仮定なし。使われ方：有限旗の共通帰納段。 -/
theorem closedTailMultiStep_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedTailMultiStep P n (r + 1))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (closedTailCompletionSection P n))) :=
    multiRealization_map_localized_isIso_of_equivalence r
      (stableTrivialPullbackSectionEquivalence (closedCofiberProjectionExact P)
        (closedArrowCofiberEquivalence P).inv (closedArrowCofiberEquivalence_section P)
        (closedTailEdge P n)).symm
  have := closedTailPair_multi_localized_isIso P n r
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (lift ((multiRealizationFunctor (r + 1)).map (closedTailPrefix P n))
      ((multiRealizationFunctor (r + 1)).map (closedTailCofiber P n))))
  rw [← closedTailCompletionSection_pair, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration

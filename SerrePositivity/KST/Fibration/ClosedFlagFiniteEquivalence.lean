module
public import SerrePositivity.KST.Fibration.ClosedFlagOneComparison
public import SerrePositivity.KST.Fibration.ClosedTailCanonicalComponents

/-!
概要：閉じた P 旗の元の有限積比較は全正有限長・全正反復で局所化同型。
方針：元の一辺加法性と全旗の相対加法性を同じ共通帰納へ代入する。
規約：核表示・Verdier 列・商比較・retract 閉包を要求しない。
使われ方：K-B2 向け元の初期評価四角形と全自然性の引き戻しの入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：一辺の有限比較を元の唯一の cofiber 因子へ戻す。
方針：同じ元の有限積射影を正規化する。
規約：元の二成分を保持。使われ方：相対加法性との厳密照合。 -/
theorem closedFlagFiniteComparison_one_normalize (r : ℕ) :
    closedFlagFiniteComparison P 1 r ≫ (𝟙 _ ⊗ₘ
      (productUniqueIso (fun _ : Fin 1 =>
        (multiRealizationFunctor r).obj (closedStableModel P))).hom) =
      lift ((multiRealizationFunctor r).map (closedFlagVertex P ⦋1⦌ 0))
        ((multiRealizationFunctor r).map (closedFlagCofiber P (𝟙 ⦋1⦌))) := by
  unfold closedFlagFiniteComparison
  rw [lift_map, Category.comp_id, productUniqueIso_hom]
  change lift _ (closedFlagConsecutiveCofibers P 1 r ≫ Pi.π _ (0 : Fin 1)) = _
  rw [closedFlagConsecutiveCofibers, Pi.lift_comp_π, consecutiveWeakStringEdge_one]

/-- 概要：元の一辺有限比較は全正反復で局所化同型。
方針：同じ相対加法性の二成分比較から元の一因子正規化同型を消去する。
規約：元の実有限比較そのもの。使われ方：共通有限旗帰納の初段。 -/
theorem closedFlagFiniteComparison_one_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedFlagFiniteComparison P 1 (r + 1))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let p := 𝟙 ((multiRealizationFunctor (r + 1)).obj B) ⊗ₘ
    (productUniqueIso (fun _ : Fin 1 =>
      (multiRealizationFunctor (r + 1)).obj (closedStableModel P))).hom
  have : IsIso p := by
    dsimp only [p]
    infer_instance
  have hn : IsIso (Q.map (closedFlagFiniteComparison P 1 (r + 1) ≫ p)) := by
    change IsIso (Q.map (closedFlagFiniteComparison P 1 (r + 1) ≫ (𝟙 _ ⊗ₘ _)))
    rw [closedFlagFiniteComparison_one_normalize]
    exact closedFlagOnePair_localized_isIso P r
  rw [Q.map_comp] at hn
  exact (isIso_comp_right_iff _ _).mp hn

/-- 概要：元の初期頂点と全連続 P cofiber の有限比較は全正長・全正反復で局所化同型。
方針：同じ実比較の初段・厳密分解・相対加法性を共通の帰納へ渡す。
規約：B と P のみ。使われ方：元の全有限旗自然性四角形の実積座標。 -/
theorem closedFlagFiniteComparison_positive_localized_isIso (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedFlagFiniteComparison P (n + 1) (r + 1))) :=
  finiteFlagComparison_positive_localized_isIso
    (fun n => (multiRealizationFunctor (r + 1)).obj (closedFlagModel P ⦋n + 1⦌))
    ((multiRealizationFunctor (r + 1)).obj B)
    ((multiRealizationFunctor (r + 1)).obj (closedStableModel P))
    (fun n => closedFlagFiniteComparison P (n + 1) (r + 1))
    (fun n => closedFlagTailMultiStep P n (r + 1))
    (fun n => closedFlagFiniteComparison_factor P n (r + 1))
    (closedFlagFiniteComparison_one_localized_isIso P r)
    (fun n => closedFlagTailMultiStep_localized_isIso P n r) n

end SerrePositivity.KST.Fibration

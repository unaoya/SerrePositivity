module

public import SerrePositivity.KST.Comparison.SpanCylinderInvariance
public import SerrePositivity.KST.Comparison.ArbitraryBasePullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# 図式の基底変換と局所化同型

概要：図式の成分ごとの Kan fibration を、終域図式の局所化同型で引き戻す。
方針：評価関手で厳密な引き戻しへ送り、既証の right properness と四角形の不変性を使う。
規約：Segal 1974 Lemma 1.7 の水平の基底射を単射に置換する還元。
使われ方：mono–trivial fibration 分解による基底 span の置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel
variable {D : Type v} [Category.{w} D] {F G H : D ⥤ SSet.{u}}

/--
概要：図式の引き戻しの各成分は、実際の単体集合の引き戻しである。
方針：評価関手の極限保存を使う。
規約：引き戻す二つの射のいずれにも Kan 性を要求しない。
使われ方：基底変換後の縦射と比較の判定。
-/
theorem diagramPullback_app_isPullback (α : F ⟶ G) (ν : H ⟶ G) (d : D) :
    IsPullback ((pullback.fst ν α).app d) ((pullback.snd ν α).app d)
      (ν.app d) (α.app d) :=
  (IsPullback.of_hasPullback ν α).map ((evaluation D SSet.{u}).obj d)

/--
概要：図式の成分ごとの Kan fibration は、任意の図式の基底変換で保たれる。
方針：各成分の厳密な引き戻しで Kan 条件を移す。
規約：置換後の基底の Kan 性は不要。
使われ方：単射な基底射への置換後の縦射の Kan 条件。
-/
theorem diagramPullback_fst_rlp (α : F ⟶ G) (ν : H ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d)) (d : D) :
    SSet.modelCategoryQuillen.J.rlp ((pullback.fst ν α).app d) :=
  SSet.modelCategoryQuillen.J.rlp.of_isPullback (diagramPullback_app_isPullback α ν d).flip (hα d)

/--
概要：成分ごとの Kan fibration に沿う局所化同型の図式の基底変換は、成分ごとに可逆である。
方針：各成分の厳密な引き戻しに任意の基底の right properness を適用する。
規約：基底図式の各対象の Kan 性は不要。
使われ方：基底 span を mono–trivial fibration 分解で置換する比較。
-/
theorem diagramPullback_snd_localized_isIso (α : F ⟶ G) (ν : H ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hν : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (ν.app d))) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((pullback.snd ν α).app d)) :=
  pullback_localized_isIso (ν.app d) (hν d) (α.app d) (hα d)
    ((pullback.snd ν α).app d) ((pullback.fst ν α).app d)
    (diagramPullback_app_isPullback α ν d).flip

/--
概要：図式の局所化可逆な基底変換は、各添字の射のホモトピー引き戻し性を保つ。
方針：二つの評価関手の下で、基底変換の比較を四頂点の局所化同型にする。
規約：元の縦射は成分ごとに Kan fibration とする。
使われ方：単射な基底の span への仮定の移送。
-/
theorem diagramPullback_arrowSquare_iff (α : F ⟶ G) (ν : H ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hν : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (ν.app d))) {d e : D} (θ : d ⟶ e) :
    IsHomotopyPullback (naturalitySquare (diagramArrow θ) (pullback.fst ν α)) ↔
      IsHomotopyPullback (naturalitySquare (diagramArrow θ) α) :=
  naturalitySquare_map_iff (diagramArrow θ) (pullback.fst ν α) α (pullback.snd ν α) ν
    (pullback.condition (f := ν) (g := α))
    (diagramPullback_snd_localized_isIso α ν hα hν d)
    (diagramPullback_snd_localized_isIso α ν hα hν e) (hν d) (hν e)

end SerrePositivity.KST.Comparison

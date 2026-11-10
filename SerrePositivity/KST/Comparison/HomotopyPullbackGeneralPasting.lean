module

public import SerrePositivity.KST.Comparison.KanSquareReplacement
public import Mathlib.Tactic.CrossRefAttribute

/-!
# ホモトピー引き戻しの一般の横の貼り合わせ

概要：縦射の Kan 性を課さず、二つのホモトピー引き戻しの外周を比較する。
方針：三つの縦射を関手的に分解し、中央が Kan な場合の証明を四頂点の不変性で移す。
規約：Segal 1974 Proposition 1.6 の有限骨格の比較への補助。
使われ方：既存の各行の比較を、次の骨格への比較と貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：二つのホモトピー引き戻しを横に貼り合わせた外周もホモトピー引き戻しである。
方針：縦射の関手的な Kan 分解へ移し、貼り合わせた外周を単位の自然性で戻す。
規約：いずれの対象にも射にも Kan 性を要求しない。
使われ方：有限骨格の帰納で、古い行の比較を次の骨格へ進める。
-/
@[kerodon 0110]
theorem isHomotopyPullback_paste_horiz
    {P X Z Y B C : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} {c : X ⟶ Z} {p : Z ⟶ C} {d : B ⟶ C}
    (s : CommSq a b f g) (t : CommSq c f p d)
    (hs : IsHomotopyPullback s) (ht : IsHomotopyPullback t) :
    IsHomotopyPullback (s.horiz_comp t) := by
  have hs' := (kanReplacementSquare_homotopyPullback_iff s).mp hs
  have ht' := (kanReplacementSquare_homotopyPullback_iff t).mp ht
  have hp := isHomotopyPullback_paste_horiz_of_middle_fibration
    (kanReplacementSquare s) (kanReplacementSquare t) hs' ht'
    (AnodyneKanReplacement.factorization.factorizationData f).hp
  apply (isHomotopyPullback_iff_of_localized_isIso
    (s.horiz_comp t) ((kanReplacementSquare s).horiz_comp (kanReplacementSquare t))
    (AnodyneKanReplacement.factorization.i.app (Arrow.mk b))
    (AnodyneKanReplacement.factorization.i.app (Arrow.mk p)) (𝟙 _) (𝟙 _)
    ?_ ?_ ?_ (by simp)
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (AnodyneKanReplacement.factorization.factorizationData b).hi)
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (AnodyneKanReplacement.factorization.factorizationData p).hi)
    (by infer_instance) (by infer_instance)).mpr hp
  · rw [Category.assoc, kanSquareTop_unit t, ← Category.assoc, kanSquareTop_unit s,
      Category.assoc]
  · rw [Category.comp_id]
    exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk b)).symm
  · rw [Category.comp_id]
    exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk p)).symm

end SerrePositivity.KST.Comparison

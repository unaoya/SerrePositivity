module
public import SerrePositivity.KST.Fibration.FibrantPullbackCancellation
public import SerrePositivity.KST.Comparison.KanSquareReplacement
public import Mathlib.Tactic.CrossRefAttribute

/-! # 実際の可換四角形のホモトピー引き戻しの右消去 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 右四角形と外周が homotopy pullback なら左四角形もそうなる。Kan 条件は不要。 -/
@[kerodon 0110]
theorem isHomotopyPullback_left_of_horiz
    {P X Z Y B C : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} {c : X ⟶ Z} {p : Z ⟶ C} {d : B ⟶ C}
    (s : CommSq a b f g) (t : CommSq c f p d)
    (hout : IsHomotopyPullback (s.horiz_comp t)) (ht : IsHomotopyPullback t) :
    IsHomotopyPullback s := by
  have ht' := (kanReplacementSquare_homotopyPullback_iff t).mp ht
  have hout' : IsHomotopyPullback
      ((kanReplacementSquare s).horiz_comp (kanReplacementSquare t)) := by
    apply (isHomotopyPullback_iff_of_localized_isIso
      (s.horiz_comp t) ((kanReplacementSquare s).horiz_comp (kanReplacementSquare t))
      (AnodyneKanReplacement.factorization.i.app (Arrow.mk b))
      (AnodyneKanReplacement.factorization.i.app (Arrow.mk p)) (𝟙 _) (𝟙 _)
      ?_ ?_ ?_ (by simp)
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
        (AnodyneKanReplacement.factorization.factorizationData b).hi)
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
        (AnodyneKanReplacement.factorization.factorizationData p).hi)
      (by infer_instance) (by infer_instance)).mp hout
    · rw [Category.assoc, kanSquareTop_unit t, ← Category.assoc, kanSquareTop_unit s,
        Category.assoc]
    · rw [Category.comp_id]
      exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk b)).symm
    · rw [Category.comp_id]
      exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk p)).symm
  apply (kanReplacementSquare_homotopyPullback_iff s).mpr
  exact isHomotopyPullback_left_of_horiz_of_middle_fibration
    (kanReplacementSquare s) (kanReplacementSquare t) hout' ht'
    (AnodyneKanReplacement.factorization.factorizationData f).hp

end SerrePositivity.KST.Fibration

module

public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs
public import SerrePositivity.KST.Comparison.AlternativePullback
public import SerrePositivity.KST.Comparison.FibrantPullbackComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# ホモトピー引き戻し性の二つの脚の対称性

概要：右の脚を置換して定義したホモトピー引き戻し性は、左右の脚を交換しても変わらない。
方針：両方の脚を Kan fibration に置換し、厳密な引き戻しの対称同型で比較する。
規約：Segal 1974 Lemma 1.7 の四角形の向きの整合。基底の Kan 性は不要。
使われ方：縦の比較が Kan fibration である厳密な引き戻しからの判定。
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
概要：ホモトピー引き戻し性は四角形の左右の脚を交換しても変わらない。
方針：四頂点の置換の不変性で両脚を Kan fibration にし、別分解の判定と引き戻しの対称性を使う。
規約：定義に用いた片方の脚の関手的な置換に依存する非対称性を取り除く。
使われ方：二重写像円筒の縦射を用いたホモトピー引き戻し性の証明。
-/
@[kerodon 010Y]
theorem isHomotopyPullback_flip_iff {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) :
    IsHomotopyPullback sq.flip ↔ IsHomotopyPullback sq := by
  let d₀ := AnodyneKanReplacement.factorization.factorizationData f
  let d₁ := AnodyneKanReplacement.factorization.factorizationData g
  have hi₀ : IsIso (AnodyneHomotopy.anodyneQ.map d₀.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ d₀.hi
  have hi₁ : IsIso (AnodyneHomotopy.anodyneQ.map d₁.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ d₁.hi
  let sqR : CommSq (a ≫ d₀.i) (b ≫ d₁.i) d₀.p d₁.p := ⟨by
    rw [Category.assoc, d₀.fac, Category.assoc, d₁.fac]
    exact sq.w⟩
  have hR : IsHomotopyPullback sq ↔ IsHomotopyPullback sqR :=
    isHomotopyPullback_iff_of_localized_isIso sq sqR (𝟙 P) d₀.i d₁.i (𝟙 Z)
      (by simp) (by simp) (by simp [d₀.fac]) (by simp [d₁.fac])
      inferInstance hi₀ hi₁ inferInstance
  have hRF : IsHomotopyPullback sq.flip ↔ IsHomotopyPullback sqR.flip :=
    isHomotopyPullback_iff_of_localized_isIso sq.flip sqR.flip (𝟙 P) d₁.i d₀.i (𝟙 Z)
      (by simp) (by simp) (by simp [d₁.fac]) (by simp [d₀.fac])
      inferInstance hi₁ hi₀ inferInstance
  let t := alternativePullbackComparison sqR (𝟙 d₁.Z) d₁.p (Category.id_comp _)
  let u := alternativePullbackComparison sqR.flip (𝟙 d₀.Z) d₀.p (Category.id_comp _)
  have ht : IsHomotopyPullback sqR ↔ IsIso (AnodyneHomotopy.anodyneQ.map t) :=
    isHomotopyPullback_iff_alternative sqR (𝟙 d₁.Z)
      (SSet.anodyneExtensions.of_isIso _) d₁.p d₁.hp (Category.id_comp _)
  have hu : IsHomotopyPullback sqR.flip ↔ IsIso (AnodyneHomotopy.anodyneQ.map u) :=
    isHomotopyPullback_iff_alternative sqR.flip (𝟙 d₀.Z)
      (SSet.anodyneExtensions.of_isIso _) d₀.p d₀.hp (Category.id_comp _)
  have htu : t = u ≫ (pullbackSymmetry d₁.p d₀.p).hom := by
    apply pullback.hom_ext
    · simp only [t, u, alternativePullbackComparison_fst, Category.assoc,
        pullbackSymmetry_hom_comp_fst, alternativePullbackComparison_snd, Category.comp_id]
    · simp only [t, u, alternativePullbackComparison_snd, Category.assoc,
        pullbackSymmetry_hom_comp_snd, alternativePullbackComparison_fst, Category.comp_id]
  have hsym : IsHomotopyPullback sqR ↔ IsHomotopyPullback sqR.flip := by
    rw [ht, hu, htu, Functor.map_comp]
    exact isIso_comp_right_iff _ _
  exact hRF.trans (hsym.symm.trans hR.symm)

/--
概要：左の脚が Kan fibration の厳密な引き戻しも、ホモトピー引き戻しである。
方針：脚を交換した四角形に右脚の判定を適用し、交換の不変性で戻す。
規約：基底の Kan 性や反対側の脚の Kan 性は不要。
使われ方：縦射が Kan fibration である円筒の各頂点の四角形。
-/
theorem isHomotopyPullback_of_left_fibration {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hf : SSet.modelCategoryQuillen.J.rlp f) :
    IsHomotopyPullback sq.toCommSq :=
  (isHomotopyPullback_flip_iff _).mp (isHomotopyPullback_of_fibration sq.flip hf)

end SerrePositivity.KST.Comparison

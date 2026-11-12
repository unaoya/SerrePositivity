module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SequentialRelativeLifting
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
概要：共通部分を持つ任意の族の相対的な持ち上げの貼り合わせ。
方針：共通部分の持ち上げを先に選び、各枝の相対比較に沿って延長する。
規約：添字は任意の小さい型、quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各次数のセルの族。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：共通部分を持つ図式の自然変換の各枝の相対比較。
方針：共通部分の終域に枝の始域を pushout で貼る。
規約：添字は WidePushoutShape の枝。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の相対セルの族。 -/
noncomputable def wideNatTransCornerMap {J : Type v}
    {F H : WidePushoutShape J ⥤ SSet.{u}} (s : F ⟶ H) (j : J) :
    pushout (s.app none) (F.map (.init j)) ⟶ H.obj (some j) :=
  pushout.desc (H.map (.init j)) (s.app (some j)) (s.naturality _).symm

/-- 概要：共通部分と各枝の相対比較が持ち上げ性を持てば wide pushout の比較も持つ。
方針：共通部分の持ち上げを固定して各枝へ延長し、余極限から射を作る。
規約：列の比較の成分の単射性はこの一般補題には不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族の貼り合わせ。 -/
lemma hasLiftingProperty_of_widePushout_relative_corners {J : Type v}
    {F H : WidePushoutShape J ⥤ SSet.{u}} (s : F ⟶ H)
    (cF : Cocone F) (cH : Cocone H) (hcF : IsColimit cF) (hcH : IsColimit cH)
    (i : cF.pt ⟶ cH.pt) (hi : ∀ n, cF.ι.app n ≫ i = s.app n ≫ cH.ι.app n)
    {E Y : SSet.{u}} (p : E ⟶ Y) [HasLiftingProperty (s.app none) p]
    [∀ j, HasLiftingProperty (wideNatTransCornerMap s j) p] : HasLiftingProperty i p := by
  classical
  constructor
  intro a b sq
  let S₀ : CommSq (cF.ι.app none ≫ a) (s.app none) p (cH.ι.app none ≫ b) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, hi, Category.assoc]⟩
  let u₀ := S₀.lift
  have hu₀ : s.app none ≫ u₀ = cF.ι.app none ≫ a := S₀.fac_left
  have hu₀p : u₀ ≫ p = cH.ι.app none ≫ b := S₀.fac_right
  have hbranch : ∀ j, ∃ u : H.obj (some j) ⟶ E,
      H.map (.init j) ≫ u = u₀ ∧ s.app (some j) ≫ u = cF.ι.app (some j) ≫ a ∧
        u ≫ p = cH.ι.app (some j) ≫ b := by
    intro j
    have hq : s.app none ≫ u₀ = F.map (.init j) ≫ (cF.ι.app (some j) ≫ a) := by
      rw [← Category.assoc, cF.w]
      exact hu₀
    let q := pushout.desc u₀ (cF.ι.app (some j) ≫ a) hq
    let S : CommSq q (wideNatTransCornerMap s j) p (cH.ι.app (some j) ≫ b) := ⟨by
      apply pushout.hom_ext
      · rw [← Category.assoc, pushout.inl_desc, hu₀p]
        change _ = pushout.inl _ _ ≫ (pushout.desc _ _ _ ≫ _)
        rw [← Category.assoc, pushout.inl_desc, ← Category.assoc, cH.w]
      · rw [← Category.assoc, pushout.inr_desc, Category.assoc, sq.w,
          ← Category.assoc, hi, Category.assoc]
        change _ = pushout.inr _ _ ≫ (pushout.desc _ _ _ ≫ _)
        rw [reassoc_of% pushout.inr_desc]⟩
    refine ⟨S.lift, ?_, ?_, S.fac_right⟩
    · have he := congrArg (fun z ↦ pushout.inl (s.app none) (F.map (.init j)) ≫ z) S.fac_left
      simpa only [wideNatTransCornerMap, q, ← Category.assoc, pushout.inl_desc] using he
    · have he := congrArg (fun z ↦ pushout.inr (s.app none) (F.map (.init j)) ≫ z) S.fac_left
      simpa only [wideNatTransCornerMap, q, ← Category.assoc, pushout.inr_desc] using he
  let C : Cocone H := WidePushoutShape.mkCocone u₀ (fun j ↦ (hbranch j).choose)
    (fun j ↦ (hbranch j).choose_spec.1)
  have hleft : i ≫ hcH.desc C = a := by
    apply hcF.hom_ext
    intro n
    rw [← Category.assoc, hi, Category.assoc, hcH.fac]
    cases n with
    | none => exact hu₀
    | some j => exact (hbranch j).choose_spec.2.1
  have hright : hcH.desc C ≫ p = b := by
    apply hcH.hom_ext
    intro n
    rw [← Category.assoc, hcH.fac]
    cases n with
    | none => exact hu₀p
    | some j => exact (hbranch j).choose_spec.2.2
  exact CommSq.HasLift.mk' { l := hcH.desc C, fac_left := hleft, fac_right := hright }

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.NaturalEquivalenceCylinder

/-!
概要：二つの可算列の相対的な持ち上げの余極限への貼り合わせ。
方針：各段階で二つの可換条件を保つ持ち上げを選び、互換な列の余極限を使う。
規約：モデル構造や quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限の骨格の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：各段階で相対的な持ち上げを延長できれば二つの列の余極限でも持ち上げられる。
方針：指定された始域と標的への合成を保持した持ち上げを自然数上で選ぶ。
規約：両列の余極限 cocone とその間の比較射を指定する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の可算の貼り合わせ。 -/
lemma exists_lift_of_sequential_relative_extensions {F H : ℕ ⥤ SSet.{u}} (s : F ⟶ H)
    (cF : Cocone F) (cH : Cocone H) (hcF : IsColimit cF) (hcH : IsColimit cH)
    (i : cF.pt ⟶ cH.pt) (hi : ∀ n, cF.ι.app n ≫ i = s.app n ≫ cH.ι.app n)
    {E Y : SSet.{u}} (p : E ⟶ Y) (a : cF.pt ⟶ E) (b : cH.pt ⟶ Y)
    (hinit : ∃ f : H.obj 0 ⟶ E,
      s.app 0 ≫ f = cF.ι.app 0 ≫ a ∧ f ≫ p = cH.ι.app 0 ≫ b)
    (hstep : ∀ n (f : H.obj n ⟶ E), s.app n ≫ f = cF.ι.app n ≫ a →
      f ≫ p = cH.ι.app n ≫ b → ∃ g : H.obj (n + 1) ⟶ E,
        H.map (homOfLE (Nat.le_succ n)) ≫ g = f ∧
          s.app (n + 1) ≫ g = cF.ι.app (n + 1) ≫ a ∧ g ≫ p = cH.ι.app (n + 1) ≫ b) :
    ∃ f : cH.pt ⟶ E, i ≫ f = a ∧ f ≫ p = b := by
  classical
  let P (n : ℕ) := {f : H.obj n ⟶ E //
    s.app n ≫ f = cF.ι.app n ≫ a ∧ f ≫ p = cH.ι.app n ≫ b}
  let init : P 0 := ⟨hinit.choose, hinit.choose_spec⟩
  have step (n : ℕ) (f : P n) : ∃ g : P (n + 1),
      H.map (homOfLE (Nat.le_succ n)) ≫ g.val = f.val := by
    obtain ⟨g, hg, hg₁, hg₂⟩ := hstep n f.val f.property.1 f.property.2
    exact ⟨⟨g, hg₁, hg₂⟩, hg⟩
  let fs : (n : ℕ) → P n := fun n ↦ Nat.rec init (fun n f ↦ (step n f).choose) n
  have hfs (n : ℕ) : H.map (homOfLE (Nat.le_succ n)) ≫ (fs (n + 1)).val = (fs n).val :=
    (step n (fs n)).choose_spec
  have hn (n m : ℕ) (hnm : n ≤ m) : H.map (homOfLE hnm) ≫ (fs m).val = (fs n).val := by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have he : (homOfLE (Nat.le_succ_of_le hm) : n ⟶ m + 1) =
          homOfLE hm ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
      rw [he, H.map_comp, Category.assoc, hfs, ih]
  let C : Cocone H :=
    { pt := E
      ι :=
        { app := fun n ↦ (fs n).val
          naturality := fun n m α ↦ by
            change H.map α ≫ (fs m).val = (fs n).val ≫ 𝟙 E
            have he : homOfLE (leOfHom α) = α := Subsingleton.elim _ _
            simpa only [Category.comp_id, he] using hn n m (leOfHom α) } }
  refine ⟨hcH.desc C, ?_, ?_⟩
  · apply hcF.hom_ext
    intro n
    rw [← Category.assoc, hi, Category.assoc, hcH.fac]
    exact (fs n).property.1
  · apply hcH.hom_ext
    intro n
    rw [← Category.assoc, hcH.fac]
    exact (fs n).property.2

/-- 概要：二つの列の自然変換の次の段階への相対比較射。
方針：前の段階の終域と次の段階の始域を pushout で貼る。
規約：添字は自然数。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各段階の持ち上げ。 -/
noncomputable def sequentialNatTransCornerMap {F H : ℕ ⥤ SSet.{u}} (s : F ⟶ H) (n : ℕ) :
    pushout (s.app n) (F.map (homOfLE (Nat.le_succ n))) ⟶ H.obj (n + 1) :=
  pushout.desc (H.map (homOfLE (Nat.le_succ n))) (s.app (n + 1))
    (s.naturality _).symm

/-- 概要：初期の比較と各段階の相対比較が持ち上げ性を持てば余極限の比較も持つ。
方針：相対比較の持ち上げで互換な延長を選び、二つの列の余極限へ貼る。
規約：列の比較の成分の単射性はこの一般補題には不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の単射の同値条件の可算の貼り合わせ。 -/
lemma hasLiftingProperty_of_sequential_relative_corners {F H : ℕ ⥤ SSet.{u}} (s : F ⟶ H)
    (cF : Cocone F) (cH : Cocone H) (hcF : IsColimit cF) (hcH : IsColimit cH)
    (i : cF.pt ⟶ cH.pt) (hi : ∀ n, cF.ι.app n ≫ i = s.app n ≫ cH.ι.app n)
    {E Y : SSet.{u}} (p : E ⟶ Y) [HasLiftingProperty (s.app 0) p]
    [∀ n, HasLiftingProperty (sequentialNatTransCornerMap s n) p] : HasLiftingProperty i p := by
  constructor
  intro a b sq
  have hinit : ∃ f : H.obj 0 ⟶ E,
      s.app 0 ≫ f = cF.ι.app 0 ≫ a ∧ f ≫ p = cH.ι.app 0 ≫ b := by
    let S : CommSq (cF.ι.app 0 ≫ a) (s.app 0) p (cH.ι.app 0 ≫ b) := ⟨by
      rw [Category.assoc, sq.w, ← Category.assoc, hi, Category.assoc]⟩
    exact ⟨S.lift, S.fac_left, S.fac_right⟩
  have hstep : ∀ n (f : H.obj n ⟶ E), s.app n ≫ f = cF.ι.app n ≫ a →
      f ≫ p = cH.ι.app n ≫ b → ∃ g : H.obj (n + 1) ⟶ E,
        H.map (homOfLE (Nat.le_succ n)) ≫ g = f ∧
          s.app (n + 1) ≫ g = cF.ι.app (n + 1) ≫ a ∧ g ≫ p = cH.ι.app (n + 1) ≫ b := by
    intro n f hf hfp
    let α : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
    have hq : s.app n ≫ f = F.map α ≫ (cF.ι.app (n + 1) ≫ a) := by
      rw [← Category.assoc, cF.w]
      exact hf
    let q := pushout.desc f (cF.ι.app (n + 1) ≫ a) hq
    let S : CommSq q (sequentialNatTransCornerMap s n) p (cH.ι.app (n + 1) ≫ b) := ⟨by
      apply pushout.hom_ext
      · rw [← Category.assoc, pushout.inl_desc, hfp]
        change _ = pushout.inl _ _ ≫ (pushout.desc _ _ _ ≫ _)
        rw [← Category.assoc, pushout.inl_desc, ← Category.assoc, cH.w]
      · rw [← Category.assoc, pushout.inr_desc, Category.assoc, sq.w,
          ← Category.assoc, hi, Category.assoc]
        change _ = pushout.inr _ _ ≫ (pushout.desc _ _ _ ≫ _)
        rw [reassoc_of% pushout.inr_desc]⟩
    refine ⟨S.lift, ?_, ?_, S.fac_right⟩
    · have he := congrArg (fun z ↦ pushout.inl (s.app n) (F.map α) ≫ z) S.fac_left
      simpa only [sequentialNatTransCornerMap, q, ← Category.assoc, pushout.inl_desc] using he
    · have he := congrArg (fun z ↦ pushout.inr (s.app n) (F.map α) ≫ z) S.fac_left
      simpa only [sequentialNatTransCornerMap, q, ← Category.assoc, pushout.inr_desc] using he
  obtain ⟨f, hf, hfp⟩ := exists_lift_of_sequential_relative_extensions s cF cH hcF hcH i hi
    p a b hinit hstep
  exact CommSq.HasLift.mk' { l := f, fac_left := hf, fac_right := hfp }

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

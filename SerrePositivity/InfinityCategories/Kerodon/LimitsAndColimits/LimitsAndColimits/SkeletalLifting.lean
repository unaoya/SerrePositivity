module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalExtension

/-!
概要：指定された標的への射を固定した相対骨格の持ち上げ。
方針：各段階の可換性も保持した互換な射を選び、余極限から持ち上げを作る。
規約：指定部分と標的の射の両方を厳密に固定する。
使われ方：Kerodon §7.1.8（Tag 02X8） の相対極限への還元。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対骨格のセルごとの可換な持ち上げは次の骨格へ貼り合わせられる。
方針：coproduct と pushout で境界の持ち上げを貼り、標的との可換性を pushout の外延性で確認する。
規約：射影 p と標的の射 b を固定する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の相対的な延長の一段。 -/
lemma exists_lift_skeletonOfMono_succ {A B X Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) (b : B ⟶ Y) (d : ℕ)
    (f : (skeletonOfMono i d : SSet.{u}) ⟶ X)
    (hfp : f ≫ p = (skeletonOfMono i d).ι ≫ b)
    (hf : ∀ c : Cell i d, ∃ F : (Δ[d] : SSet.{u}) ⟶ X,
      (boundary d).ι ≫ F = c.ιSigmaBoundary ≫ t i d ≫ f ∧ F ≫ p = c.map ≫ b) :
    ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X,
      r i d ≫ F = f ∧ F ≫ p = (skeletonOfMono i (d + 1)).ι ≫ b := by
  classical
  let g : sigmaStdSimplex i d ⟶ X := Sigma.desc (fun c ↦ (hf c).choose)
  have hg : l i d ≫ g = t i d ≫ f := by
    apply Sigma.hom_ext
    intro c
    rw [← Category.assoc, Cell.ι_l, Category.assoc]
    change (boundary d).ι ≫
      (Sigma.ι (fun _ : Cell i d ↦ (Δ[d] : SSet.{u})) c ≫ g) = _
    rw [Sigma.ι_comp_desc]
    exact (hf c).choose_spec.1
  let F := (isPushout i d).desc f g hg.symm
  have hF : r i d ≫ F = f := (isPushout i d).inl_desc _ _ _
  refine ⟨F, hF, ?_⟩
  apply (isPushout i d).hom_ext
  · simp only [← Category.assoc, hF, hfp]
    rfl
  · rw [← Category.assoc, (isPushout i d).inr_desc]
    apply Sigma.hom_ext
    intro c
    have hgc : c.ιSigmaStdSimplex ≫ g = (hf c).choose := Sigma.ι_comp_desc _ _
    have hbc : c.ιSigmaStdSimplex ≫ SSet.relativeCellComplexOfMono.b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ b =
        c.map ≫ b := by
      simpa only [Category.assoc] using congrArg (fun j ↦ j ≫ b) c.ι_b_ι
    change c.ιSigmaStdSimplex ≫ (g ≫ p) =
      c.ιSigmaStdSimplex ≫ SSet.relativeCellComplexOfMono.b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ b
    rw [← Category.assoc c.ιSigmaStdSimplex g p, hgc, hbc]
    exact (hf c).choose_spec.2

/-- 概要：全ての骨格で可換な持ち上げを延長できれば全体でも持ち上げられる。
方針：指定部分と射影の可換性を保持した射を自然数上で選び、相対骨格の余極限を使う。
規約：単射の始域上の射 a と標的の射 b を固定する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の相対的なセル延長。 -/
lemma exists_lift_of_skeletal_lifts {A B X Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (hw : a ≫ p = i ≫ b)
    (hstep : ∀ d (f : (skeletonOfMono i d : SSet.{u}) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i d ≫ f = a → f ≫ p = (skeletonOfMono i d).ι ≫ b →
        ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X,
          r i d ≫ F = f ∧ F ≫ p = (skeletonOfMono i (d + 1)).ι ≫ b) :
    ∃ F : B ⟶ X, i ≫ F = a ∧ F ≫ p = b := by
  classical
  let P (d : ℕ) := { f : (skeletonOfMono i d : SSet.{u}) ⟶ X //
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i d ≫ f = a ∧ f ≫ p = (skeletonOfMono i d).ι ≫ b }
  have hinit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a) = a := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso_inv, Iso.inv_hom_id_assoc]
  have hinitp : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a) ≫ p = (skeletonOfMono i 0).ι ≫ b := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).inv).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso_inv]
    calc
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a) ≫ p) = a ≫ p := by
        rw [← Category.assoc, hinit]
      _ = i ≫ b := hw
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ (skeletonOfMono i 0).ι ≫ b := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase, Subcomplex.lift_ι_assoc]
  let init : P 0 := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso i).hom ≫ a, hinit, hinitp⟩
  have step (d : ℕ) (f : P d) : ∃ F : P (d + 1), r i d ≫ F.val = f.val := by
    obtain ⟨F, hF, hFp⟩ := hstep d f.val f.property.1 f.property.2
    refine ⟨⟨F, ?_, hFp⟩, hF⟩
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase_succ i d, Category.assoc, hF]
    exact f.property.1
  let fs : (d : ℕ) → P d := fun d ↦ Nat.rec init (fun n f ↦ (step n f).choose) d
  have hfs (d : ℕ) : r i d ≫ (fs (d + 1)).val = (fs d).val :=
    (step d (fs d)).choose_spec
  let c := SSet.relativeCellComplexOfMono i
  have hn (n m : ℕ) (hnm : n ≤ m) :
      c.F.map (homOfLE hnm) ≫ (fs m).val = (fs n).val := by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have he : (homOfLE (Nat.le_succ_of_le hm) : n ⟶ m + 1) =
          homOfLE hm ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
      rw [he, CategoryTheory.Functor.map_comp, Category.assoc]
      change c.F.map (homOfLE hm) ≫ (r i m ≫ (fs (m + 1)).val) = _
      rw [hfs, ih]
  let C : Cocone c.F :=
    { pt := X
      ι :=
        { app := fun n ↦ (fs n).val
          naturality := fun n m α ↦ by
            change c.F.map α ≫ (fs m).val = (fs n).val ≫ 𝟙 X
            have hα : homOfLE (leOfHom α) = α := Subsingleton.elim _ _
            simpa only [Category.comp_id, hα] using hn n m (leOfHom α) } }
  refine ⟨c.isColimit.desc C, ?_, ?_⟩
  · have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ c.incl.app 0 = i := Subcomplex.lift_ι _ _
    calc
      i ≫ c.isColimit.desc C = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ c.incl.app 0) ≫ c.isColimit.desc C :=
        congrArg (fun j ↦ j ≫ c.isColimit.desc C) hi.symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i 0 ≫ (fs 0).val := by rw [Category.assoc, c.isColimit.fac C 0]
      _ = a := (fs 0).property.1
  · apply c.isColimit.hom_ext
    intro n
    rw [← Category.assoc, c.isColimit.fac C n]
    exact (fs n).property.2

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

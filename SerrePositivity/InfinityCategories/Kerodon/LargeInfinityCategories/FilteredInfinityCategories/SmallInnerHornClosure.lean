module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SmallSubcomplexStages
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.Basic.Countable.Small

/-!
概要：指定された小さい部分複体を含む、小さい内ホーン充填閉包。
方針：各段階の全内ホーンに充填単体を一つずつ加え、可算和を取る。
規約：元の ambient quasicategory 内で構成し、straightening とモデル構造に依存しない。
使われ方：Ind-S (4) の局所化の宇宙持ち上げ。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 内ホーンの全試験族。面の互換性は元の実射が保持する。 -/
abbrev InnerHornData (A : SSet.{v}) :=
  Σ n : ℕ, Σ i : {i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2)},
    ((Λ[n + 2, i.val] : SSet.{v}) ⟶ A)

/-- 小さい単体集合に入る内ホーンの試験族は同じ宇宙で小さい。 -/
lemma small_innerHornData (A : SSet.{v}) [∀ d, Small.{u} (A.obj d)] :
    Small.{u} (InnerHornData A) := by
  have (n : ℕ) (i : Fin (n + 3)) :
      Small.{u} ((Λ[n + 2, i] : SSet.{v}) ⟶ A) := by
    have (d : SimplexCategoryᵒᵖ) : Small.{u} ((Λ[n + 2, i] : SSet.{v}).obj d) := by
      infer_instance
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_hom _ _
  infer_instance

/-- 元の ambient quasicategory で選択する同じ内ホーンの実充填。 -/
def innerHornFiller {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (h : InnerHornData A.toSSet) : (Δ[h.1 + 2] : SSet.{v}) ⟶ X :=
  (Quasicategory.hornFilling h.2.1.property.1 h.2.1.property.2 (h.2.2 ≫ A.ι)).choose

/-- 選んだ実単体は元の全ホーンを厳密に充填する。 -/
lemma innerHornFiller_spec {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (h : InnerHornData A.toSSet) :
    h.2.2 ≫ A.ι = (horn (h.1 + 2) h.2.1.val).ι ≫ innerHornFiller A h :=
  (Quasicategory.hornFilling h.2.1.property.1 h.2.1.property.2 (h.2.2 ≫ A.ι)).choose_spec

/-- 一段で元の部分複体と全内ホーンの選択充填を保持する。 -/
def innerHornStep {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) : X.Subcomplex :=
  A ⊔ ⨆ h : InnerHornData A.toSSet, SSet.Subcomplex.range (innerHornFiller A h)

/-- 一段の内ホーン充填は、各次数の小ささを保つ。 -/
lemma small_innerHornStep {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    [∀ d, Small.{u} (A.obj d)] (d : SimplexCategoryᵒᵖ) :
    Small.{u} ((innerHornStep A).obj d) := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (A.toSSet.obj d) :=
    inferInstanceAs (Small.{u} (A.obj d))
  have : Small.{u} (InnerHornData A.toSSet) := small_innerHornData.{u, v} A.toSSet
  have (h : InnerHornData A.toSSet) (d : SimplexCategoryᵒᵖ) :
      Small.{u} ((SSet.Subcomplex.range (innerHornFiller A h)).obj d) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u, v} (innerHornFiller A h) d
  have : Small.{u} ((⨆ h : InnerHornData A.toSSet,
      SSet.Subcomplex.range (innerHornFiller A h)).obj d) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_iSup _ d
  change Small.{u} (A.obj d ∪ (⨆ h : InnerHornData A.toSSet,
    SSet.Subcomplex.range (innerHornFiller A h)).obj d : Set (X.obj d))
  infer_instance

/-- 元の種を保つ内ホーン充填の可算段階。 -/
def innerHornStage {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) : ℕ → X.Subcomplex
  | 0 => A
  | n + 1 => innerHornStep (innerHornStage A n)

lemma innerHornStage_mono {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) :
    Monotone (innerHornStage A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_sup_left

lemma small_innerHornStage {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    [∀ d, Small.{u} (A.obj d)] (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    Small.{u} ((innerHornStage A n).obj d) := by
  induction n generalizing d with
  | zero => simpa only [innerHornStage] using (inferInstance : Small.{u} (A.obj d))
  | succ n ih =>
    have (d : SimplexCategoryᵒᵖ) : Small.{u} ((innerHornStage A n).obj d) := ih d
    exact small_innerHornStep _ d

/-- 全段階の和である、元の ambient 内の内ホーン充填閉包。 -/
def innerHornClosure {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) : X.Subcomplex :=
  ⨆ n, innerHornStage A n

lemma le_innerHornClosure {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) :
    A ≤ innerHornClosure A := le_iSup (innerHornStage A) 0

lemma small_innerHornClosure {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    [∀ d, Small.{u} (A.obj d)] (d : SimplexCategoryᵒᵖ) :
    Small.{u} ((innerHornClosure A).obj d) := by
  have (n : ℕ) (d : SimplexCategoryᵒᵖ) : Small.{u} ((innerHornStage A n).obj d) :=
    small_innerHornStage A n d
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_iSup _ d

/-- 元の標準単体とホーンは有限個の非退化単体で生成される。 -/
private lemma horn_finite (n : ℕ) (i : Fin (n + 1)) : (Λ[n, i] : SSet.{v}).Finite := by
  have : (Δ[n] : SSet.{v}).Finite := SSet.finite_of_hasDimensionLT _ (n + 1)
    (fun _ _ => inferInstance)
  infer_instance

/-- 閉包自身の全内ホーンが、同じ閉包内で厳密に充填される。 -/
instance innerHornClosure_quasicategory {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex) :
    Quasicategory (innerHornClosure A).toSSet where
  hornFilling' {n i} a h0 hn := by
    have : (Λ[n + 2, i] : SSet.{v}).Finite := horn_finite _ _
    let f := a ≫ (innerHornClosure A).ι
    have hf : SSet.Subcomplex.range f ≤ innerHornClosure A := by
      intro d y hy
      obtain ⟨x, rfl⟩ := hy
      exact (a.app d x).property
    obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_range_le_stage (innerHornStage A) (innerHornStage_mono A) f hf
    let h : InnerHornData (innerHornStage A k).toSSet :=
      ⟨n, ⟨i, h0, hn⟩, (innerHornStage A k).lift f hk⟩
    have ht : SSet.Subcomplex.range (innerHornFiller (innerHornStage A k) h) ≤
        innerHornClosure A := le_trans
      (le_trans (le_iSup (fun h : InnerHornData (innerHornStage A k).toSSet =>
        SSet.Subcomplex.range (innerHornFiller (innerHornStage A k) h)) h) le_sup_right)
      (le_iSup (innerHornStage A) (k + 1))
    refine ⟨(innerHornClosure A).lift (innerHornFiller (innerHornStage A k) h) ht, ?_⟩
    apply (cancel_mono (innerHornClosure A).ι).1
    rw [Category.assoc, SSet.Subcomplex.lift_ι]
    simpa only [h, SSet.Subcomplex.lift_ι] using innerHornFiller_spec (innerHornStage A k) h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

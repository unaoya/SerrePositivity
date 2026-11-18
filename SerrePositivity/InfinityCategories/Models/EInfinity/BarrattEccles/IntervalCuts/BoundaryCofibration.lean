module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RelativeLifting

/-!
模型。文献の定義との比較は後で
# 正規化区間の二端点境界は射影 cofibration

概要：Berger–Moerdijk 命題 4.1・Berger–Fresse §3.1 の具体区間の境界条件を証明する。
方針：生成 cofibration の右持ち上げ類を全射な擬同型と同定し、両端点固定の lift を使う。
規約：モデル構造や始域の cofibrancy は仮定しない。
使われ方：具体的な E-coalgebra 区間の boundary_cofibration フィールド。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：二端点の直和から実際の正規化区間への包含（BM 命題 4.1）。
方針：実際の二つの端点射の余積射を取る。
規約：左が false、右が true。
使われ方：区間の cofibration 条件と境界を保つ持ち上げ。 -/
def boundary : (𝟙_ (Complex A)) ⊞ (𝟙_ (Complex A)) ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A :=
  biprod.desc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A false) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A true)

/-- 概要：二端点境界の後の収縮は単位複体の fold 射（BM 命題 4.1）。
方針：直和の二つの包含で比較して端点・収縮の三角形を使う。
規約：両端点で同じ恒等射。
使われ方：具体的な区間の底の cylinder 分解。 -/
lemma boundary_contraction : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary A ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A = biprod.desc (𝟙 _) (𝟙 _) := by
  apply biprod.hom_ext'
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, biprod.inl_desc_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_contraction, biprod.inl_desc]
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, biprod.inr_desc_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_contraction, biprod.inr_desc]

/-- 概要：実際の二端点境界は射影 cofibration（BM 命題 4.1、BF §3.1）。
方針：全射な擬同型に対して両端点を固定した区間射を持ち上げる。
規約：生成類の左持ち上げ性で述べ、モデル構造の instance は使わない。
使われ方：CoalgebraInterval の boundary_cofibration フィールド。 -/
lemma boundary_cofibration : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary A) := by
  intro K L q hq
  rw [_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations_rlp] at hq
  constructor
  intro a b sq
  have h₀ : ((biprod.inl : 𝟙_ (Complex A) ⟶ _) ≫ a) ≫ q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A false ≫ b := by
    have H := congrArg (fun f => (biprod.inl : 𝟙_ (Complex A) ⟶ _) ≫ f) sq.w
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, Category.assoc, biprod.inl_desc_assoc] using H
  have h₁ : ((biprod.inr : 𝟙_ (Complex A) ⟶ _) ≫ a) ≫ q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A true ≫ b := by
    have H := congrArg (fun f => (biprod.inr : 𝟙_ (Complex A) ⟶ _) ≫ f) sq.w
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, Category.assoc, biprod.inr_desc_assoc] using H
  obtain ⟨l, hl₀, hl₁, hlq⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_relative_lift A q hq.1 hq.2
    (biprod.inl ≫ a) (biprod.inr ≫ a) b h₀ h₁
  apply CommSq.HasLift.mk'
  refine { l := l, fac_left := ?_, fac_right := hlq }
  apply biprod.hom_ext'
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, biprod.inl_desc_assoc] using hl₀
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary, biprod.inr_desc_assoc] using hl₁

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

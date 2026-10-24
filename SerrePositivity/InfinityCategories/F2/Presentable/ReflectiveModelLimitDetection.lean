module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableSmallLimits

/-!
概要：presentable の反映模型の元の小極限を、小さい生成圏上の前層評価で検出する。
方針：全同値・反映包含・前層の各点判定を同じ全錐に順に適用する。
規約：評価の標的は宇宙 u の空間圏で、元の標的圏を大きくしない。
使われ方：元の presentable 図式の生成対象に関する極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：反映包含は元の全錐の極限性を保存し反映する。
方針：右随伴保存と全部分複体による反映を合わせる。
規約：形状は任意の単体集合。
使われ方：前層での極限検出への接続。 -/
lemma reflective_isLimitCone_iff_inclusion {K X : SSet.{u}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P)
    {D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCone D) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone (fullSubcomplexOnVertices X P).ι c) :=
  ⟨mapJoinCone_isLimit_of_adjunction r.adjunction c, isLimitCone_of_fullSubcomplex P c⟩

/-- 概要：反映 Ind 模型で、元の全錐の極限性は生成圏上の全評価で検出される。
方針：元の全同値・包含・評価の三段階を同じ錐に適用する。
規約：評価の値域は元の小さい空間圏。
使われ方：presentable 圏の小極限の各点計算。 -/
lemma reflectiveIndModel_isLimitCone_iff_evaluation
    {κ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C]
    (r : ReflectiveSubcategory (PresheafInfinity A) (IsIndVertex κ A))
    (e : QCatEquivalence (IndInfinity κ A) C)
    {K : SSet.{u}} {D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C} (c : JoinCone D) :
    IsLimitCone c ↔ ∀ a : A _⦋0⦌,
      IsLimitCone (mapJoinCone
        (e.inv ≫ indInclusionPresheaf κ A ≫ presheafInfinityEvaluation a) c) := by
  have hI := e.symm.isLimitCone_iff c
  have hP := reflective_isLimitCone_iff_inclusion r (mapJoinCone e.inv c)
  have hE := presheafInfinity_small_isLimit_iff_evaluation
    ((D ≫ e.inv) ≫ indInclusionPresheaf κ A)
    (mapJoinCone (indInclusionPresheaf κ A) (mapJoinCone e.inv c))
  simpa only [mapJoinCone, Category.assoc] using (hI.trans hP).trans hE

/-- 概要：presentable 圏には全小極限を検出する小さい前層評価の族が存在する。
方針：構成した反映 Ind 模型で全図式に共通の検出関手を固定する。
規約：対象・図式ごとに生成圏や比較を選び直さない。
使われ方：小さい生成圏での全小極限の一括判定。 -/
lemma IsPresentable.exists_limitDetectingPresheafModel {C : SSet.{u + 1}}
    [Quasicategory C] (hC : IsPresentable C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      ∃ R : C ⟶ PresheafInfinity A, ∀ (K : SSet.{u})
        (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) (c : JoinCone D),
        IsLimitCone c ↔ ∀ a : A _⦋0⦌,
          IsLimitCone (mapJoinCone (R ≫ presheafInfinityEvaluation a) c) := by
  obtain ⟨κ, hκ, A, hA, ⟨r⟩, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  have := hA
  refine ⟨A, hA, e.inv ≫ indInclusionPresheaf κ A, ?_⟩
  intro K D c
  simpa only [mapJoinCone, Category.assoc] using reflectiveIndModel_isLimitCone_iff_evaluation r e c

end SerrePositivity.InfinityCategories.F2.Presentable

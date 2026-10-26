module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.IsofibrationCriterion
public import SerrePositivity.InfinityCategories.F1.Categories.CoreKan

/-!
概要：元の core 包含は、指定された可逆辺と圏論的同値を全図式で持ち上げる。
方針：周囲の内ホーン充填の core 所属と、同じ可逆一次単体の core 所属を照合する。
規約：元の core 包含そのものを使い、可逆辺の一次単体を選び直さない。
使われ方：零次商比較の全錐比較を core の slice へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma coreInclusion_innerFibration (X : SSet.{u}) : InnerFibration (quasicategoryCore X).ι where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i h₀ hlast =>
      constructor
      intro a b sq
      let σ : (quasicategoryCore X : SSet.{u}) _⦋n + 2⦌ :=
        ⟨SSet.yonedaEquiv b, quasicategoryCore_horn_filler_mem n i a b sq.w.symm⟩
      let F : (Δ[n + 2] : SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}) :=
        SSet.yonedaEquiv.symm σ
      have hF : F ≫ (quasicategoryCore X).ι = b := by
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp]
        exact congrArg Subtype.val (SSet.yonedaEquiv.apply_symm_apply σ)
      exact ⟨F, (cancel_mono (quasicategoryCore X).ι).mp
        (by rw [Category.assoc, hF]; exact sq.w.symm), hF⟩

lemma coreInclusion_equivalenceLifting (X : SSet.{u}) [Quasicategory X] :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (quasicategoryCore X).ι := by
  have := coreInclusion_innerFibration X
  apply SerrePositivity.InfinityCategories.F1B.equivalenceLifting_of_innerFibration_of_targetLifting
  intro x e he ht
  let σ : (quasicategoryCore X : SSet.{u}) _⦋1⦌ :=
    ⟨SSet.yonedaEquiv e, (quasicategoryCore_mem_edge_iff _).mpr he⟩
  let l : (Δ[1] : SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}) := SSet.yonedaEquiv.symm σ
  have hl : l ≫ (quasicategoryCore X).ι = e := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact congrArg Subtype.val (SSet.yonedaEquiv.apply_symm_apply σ)
  refine ⟨l, ?_, hl, ?_⟩
  · apply (cancel_mono (quasicategoryCore X).ι).mp
    rw [Category.assoc, hl, ht, SSet.yonedaEquiv_symm_comp]
  · exact @IsGroupoid.all_isIso (hoFunctor.obj (quasicategoryCore X : SSet.{u})) _
      (kanComplex_ho_isGroupoid _) _ _ _

end SerrePositivity.KST.LocalizingInvariants

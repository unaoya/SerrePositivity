module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：二つの前合成同値を持つ単射の pullback 四角形で、指定した両部分の図式を延長する。
方針：二部分の pushout への包含を同値かつ単射とし、厳密な前合成の全射性を使う。
規約：充填性を要求するのは値域だけ。
使われ方：相対指数の制限の inner fibration 性に必要な、図式を固定した延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：同値な横辺を持つ単射の pullback 四角形では、両部分の整合する図式を延長できる。
方針：交わりからの pushout を作り、全体への単射の前合成同値を二対三則で得る。
規約：図式は二部分の両方で厳密に固定する。
使われ方：内ホーン上の図式と制限先の図式を同時に固定する。 -/
lemma exists_kanPrecompositionSquare_extension {A B C T D : SSet.{u}} [Quasicategory D]
    (i : A ⟶ B) (g : A ⟶ C) (k : B ⟶ T) (j : C ⟶ T)
    [Mono i] [Mono k] [Mono j] (hs : IsPullback i g k j)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j)
    (F : B ⟶ D) (G : C ⟶ D) (hFG : i ≫ F = g ≫ G) :
    ∃ H : T ⟶ D, k ≫ H = F ∧ j ≫ H = G := by
  let hp := IsPushout.of_hasPushout i g
  let m := hp.desc k j hs.w
  have : Mono m := hp.desc_mono_of_isPullback hs
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pushout.inr i g) := hi.of_isPushout hp
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m := by
    apply he.cancel_left
    rw [show pushout.inr i g ≫ m = j from hp.inr_desc _ _ _]
    exact hj
  let U := hp.desc F G hFG
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pre_surjective_of_essentiallySurjective m
    (hm D).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)
  obtain ⟨H, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).surjective v
  have hH : m ≫ H = U := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).injective hv
  refine ⟨H, ?_, ?_⟩
  · rw [← hp.inl_desc k j hs.w, Category.assoc, hH]
    exact hp.inl_desc F G hFG
  · rw [← hp.inr_desc k j hs.w, Category.assoc, hH]
    exact hp.inr_desc F G hFG

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

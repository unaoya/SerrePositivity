module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCoslice
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCosliceUncurry
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCosliceUniversal

/-! # 右因子の coproduct と join

概要：共通の左因子を持つ二つの余錐を、右因子の coproduct で貼り合わせる。
方針：通常の coslice と太い coslice の普遍性を使う。
規約：quasicategory 性を必要としない。使われ方：余錐の族の同型判定。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：右因子の coproduct との join は共通の左因子で貼った pushout。
方針：coslice の普遍性と coproduct の普遍性を組み合わせる。
規約：左図式を固定する。使われ方：余錐の可逆円柱の二端。 -/
lemma join_right_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (coprod.inr : B ⟶ A ⨿ B)) := by
  apply IsPushout.mk'
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (A ⨿ B) ≫ φ
    have hψ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (A ⨿ B) ≫ ψ = p := by
      have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ z) h₁
      simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] using he.symm
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry φ rfl = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_precomp]
        congr 1
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry_precomp]
        congr 1
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry] using congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry hc
  · intro X b c hbc
    let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ b
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K B ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p := coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry b rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry c hc)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry F, ?_, ?_⟩
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp]
      rw [coprod.inl_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp]
      rw [coprod.inr_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]


/-- 概要：右因子の coproduct との fatJoin は共通の左因子で貼った pushout。
方針：coslice の普遍性と coproduct の普遍性を組み合わせる。
規約：左図式を固定する。使われ方：余錐の可逆円柱の二端。 -/
lemma fatJoin_right_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) (coprod.inr : B ⟶ A ⨿ B)) := by
  apply IsPushout.mk'
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (A ⨿ B) ≫ φ
    have hψ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (A ⨿ B) ≫ ψ = p := by
      have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ z) h₁
      simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp] using he.symm
    have hc : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry φ rfl = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry_precomp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry_precomp]
        congr 1
      · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry_precomp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry_precomp]
        congr 1
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_curry] using congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry hc
  · intro X b c hbc
    let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ b
    have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K B ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p := coprod.desc (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry b rfl) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurry c hc)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry F, ?_, ?_⟩
    · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_precomp]
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry.{u} ((coprod.inl : A ⟶ A ⨿ B) ≫ F) = b
      rw [coprod.inl_desc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_curry]
    · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_precomp]
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry.{u} ((coprod.inr : B ⟶ A ⨿ B) ≫ F) = c
      rw [coprod.inr_desc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_curry]


end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

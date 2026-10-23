module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.KST.NonConnective.DGKappaConeInput

/-!
概要：κ 未満自由 sphere の実小代表族と、射影的代表集合の導来 ∞ 比較を構成する。
方針：小さい ordinal 添字と実直和表示、β5 の全関手比較を保持する。
規約：全共変 Hom による κ-compact 性や全 κ-compact 被覆はここでは結論しない。
使われ方：K-7 に供給する実 κ-compact dg 小模型の出発点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve

lemma dgProjectiveSubcategoryConeDerived_isFullyFaithful
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (S : Set (ModuleCategory R D))
    (hS : ∀ M, S M → moduleHomotopicallyProjective R D M) :
    IsFullyFaithful
      (dgNerve.map (dgFullSubcategoryInclusion R (ModuleCategory R D) S) ≫
        SerrePositivity.KST.NonConnective.dgConeModuleDerived R D) := by
  let H := dgFullSubcategoryInclusion R (ModuleCategory R D) S
  let F := SerrePositivity.KST.NonConnective.dgConeModuleForget R D
  have hProj : ∀ M : {M : ModuleCategory R D // S M},
      dgModuleProjectiveProperty R D ((H.comp F).obj M) := by
    intro M
    exact hS M.val M.property
  have hHom : ∀ M N : {M : ModuleCategory R D // S M}, IsIso ((H.comp F).map M N) := by
    intro M N
    change IsIso (𝟙 _ ≫ 𝟙 _)
    infer_instance
  have hh := dgModuleResolvedInfinity_isFullyFaithful_of_projective_homIso
    R _ D (H.comp F) hProj hHom
  exact (FunctorIso.isFullyFaithful_iff
    (dgModuleResolvedInfinity_precompIso R _ _ D H F)).mp hh

end SerrePositivity.InfinityCategories

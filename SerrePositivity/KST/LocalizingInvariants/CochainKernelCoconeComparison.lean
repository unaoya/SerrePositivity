module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeZeroLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionHomExt

/-!
概要：実 kernel の零比較による持ち上げは、cocone 間の標準射の実 kernel である。
方針：元の二射影で消滅条件を回収し、kernel の普遍性を cocone へ移す。
規約：全射性は不要、比較 cochain は零。使われ方：通常 pullback と導来模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (d : K ⟶ L)

def cochainKernelToCocone : kernel d ⟶ mappingCocone d :=
  mappingCocone.lift d (kernel.ι d) 0 (by simp)

@[reassoc] lemma cochainKernelToCocone_fst :
    cochainKernelToCocone d ≫ mappingCocone.fst d = kernel.ι d :=
  mappingCocone.lift_fst _ _ _ _

lemma cochainKernelToCocone_snd :
    (Cochain.ofHom (cochainKernelToCocone d)).comp (mappingCocone.snd d)
      (zero_add (-1)) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v]
  exact mappingCocone.lift_f_snd_v d (kernel.ι d) 0 (by simp) p q hpq

def cochainCoconeToIdentity : mappingCocone d ⟶ mappingCocone (𝟙 L) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d (𝟙 L) d (𝟙 L) (by simp)

@[reassoc] lemma cochainCoconeToIdentity_fst :
    cochainCoconeToIdentity d ≫ mappingCocone.fst (𝟙 L) = mappingCocone.fst d ≫ d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst _ _ _ _ _

lemma cochainCoconeToIdentity_snd :
    (Cochain.ofHom (cochainCoconeToIdentity d)).comp (mappingCocone.snd (𝟙 L))
      (zero_add (-1)) = mappingCocone.snd d := by
  rw [cochainCoconeToIdentity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  simp

lemma cochainKernelToCocone_condition :
    cochainKernelToCocone d ≫ cochainCoconeToIdentity d = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (𝟙 L)
  · rw [Category.assoc, cochainCoconeToIdentity_fst, ← Category.assoc,
      cochainKernelToCocone_fst, kernel.condition, zero_comp]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      cochainCoconeToIdentity_snd, cochainKernelToCocone_snd]
    simp

lemma cochainCoconeToIdentity_zero_fst {W : Complex R}
    (a : W ⟶ mappingCocone d) (ha : a ≫ cochainCoconeToIdentity d = 0) :
    (a ≫ mappingCocone.fst d) ≫ d = 0 := by
  have h := congrArg (fun t => t ≫ mappingCocone.fst (𝟙 L)) ha
  simpa only [Category.assoc, cochainCoconeToIdentity_fst, zero_comp] using h

lemma cochainCoconeToIdentity_zero_snd {W : Complex R}
    (a : W ⟶ mappingCocone d) (ha : a ≫ cochainCoconeToIdentity d = 0) :
    (Cochain.ofHom a).comp (mappingCocone.snd d) (zero_add (-1)) = 0 := by
  have h := congrArg (fun t => (Cochain.ofHom t).comp
    (mappingCocone.snd (𝟙 L)) (zero_add (-1))) ha
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    cochainCoconeToIdentity_snd] at h
  simpa using h

def cochainKernelToCocone_isKernel : IsLimit
    (KernelFork.ofι (cochainKernelToCocone d) (cochainKernelToCocone_condition d)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun a ha =>
    kernel.lift d (a ≫ mappingCocone.fst d) (cochainCoconeToIdentity_zero_fst d a ha)) ?_ ?_
  · intro W a ha
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d
    · rw [Category.assoc, cochainKernelToCocone_fst, kernel.lift_ι]
    · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
        cochainKernelToCocone_snd, Cochain.comp_zero]
      exact (cochainCoconeToIdentity_zero_snd d a ha).symm
  · intro W a ha m hm
    apply (cancel_mono (kernel.ι d)).1
    rw [kernel.lift_ι, ← cochainKernelToCocone_fst d, ← Category.assoc, hm]

end SerrePositivity.KST.LocalizingInvariants

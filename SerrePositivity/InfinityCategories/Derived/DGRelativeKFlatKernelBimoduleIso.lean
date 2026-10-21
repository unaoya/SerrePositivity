module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIso
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIsoRecovery
/-!
概要：双加群同型の通常 kernel 作用を K-flat の実完全充満包含で回収する。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ双加群同型の通常作用を K-flat 圏の全関手同型へ持ち上げる。 -/
def dgRelativeKFlatKernelBimoduleIso {P Q : BimoduleCategory R E D} (e : P ≅ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    FunctorIso (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ) := by
  have ee : FunctorIso
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
        dgRelativeKFlatModuleInclusion R E)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ ≫
        dgRelativeKFlatModuleInclusion R E) := by
    rw [dgRelativeKFlatKernelNerve_inclusion, dgRelativeKFlatKernelNerve_inclusion]
    exact (dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
      (dgRelativeKFlatModuleInclusion R D)
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E)
    (dgModuleRelativeKFlatVertex R E)).preimageFunctorIso ee
/-- 持ち上げた同型は、実包含後に元の指定 nerve 同型を回収する。 -/
lemma dgRelativeKFlatKernelBimoduleIso_inclusion_heq
    {P Q : BimoduleCategory R E D} (e : P ≅ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    HEq ((dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp
      (dgRelativeKFlatModuleInclusion R E))
      ((dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp
        (dgRelativeKFlatModuleInclusion R D)) := by
  dsimp -zeta only [dgRelativeKFlatKernelBimoduleIso]
  extract_lets ee
  have hf : IsFullyFaithful (dgRelativeKFlatModuleInclusion R E) :=
    isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E) (dgModuleRelativeKFlatVertex R E)
  have h := hf.preimageFunctorIso_postcomp ee
  apply (heq_of_eq h).trans
  simp only [ee, Eq.mpr]
  rfl
end
end SerrePositivity.InfinityCategories

module

public import SerrePositivity.KST.LocalizingInvariants.CochainConeMapQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
概要：実 kernel の準同型表示から、cone による元の商射の準同型分解を作る。
方針：kernel の短完全列の cone 比較へ、元の表示の cone 射を合成する。
規約：複体の分解であり、代数構造は別に検証する。使われ方：Postnikov derivation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {M K L : Complex R}
  (i : M ⟶ K) (q : K ⟶ L) (h : i ≫ q = 0)

def cochainConeQuotient : mappingCone i ⟶ L := mappingCone.desc i 0 q (by simp [h])

@[reassoc] lemma cochainConeQuotient_inr :
    mappingCone.inr i ≫ cochainConeQuotient i q h = q := mappingCone.inr_desc _ _ _ _

lemma cochainConeQuotient_epi [Epi q] : Epi (cochainConeQuotient i q h) :=
  epi_of_epi_fac (cochainConeQuotient_inr i q h)

lemma cochainConeQuotient_kernel_comparison :
    mappingCone.map i (kernel.ι q) (kernel.lift q i h) (𝟙 K) (by simp) ≫
      mappingCone.descShortComplex (cochainKernelSequence q) = cochainConeQuotient i q h := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from i (n + 1) n rfl
  · simp [mappingCone.map, cochainConeQuotient, mappingCone.descShortComplex,
      cochainKernelSequence]
  · simp [mappingCone.map, cochainConeQuotient, mappingCone.descShortComplex,
      cochainKernelSequence]

lemma cochainConeQuotient_quasiIso [Epi q] (ha : QuasiIso (kernel.lift q i h)) :
    QuasiIso (cochainConeQuotient i q h) := by
  rw [← cochainConeQuotient_kernel_comparison]
  exact quasiIso_comp _ _
    (hφ := cochainConeMap_quasiIso _ _ _ _ _ ha (quasiIso_of_isIso _))
    (hφ' := mappingCone.quasiIso_descShortComplex (cochainKernelSequence_shortExact q))

lemma cochainConeQuotient_naturality {M' K' L' : Complex R}
    (i' : M' ⟶ K') (q' : K' ⟶ L') (h' : i' ≫ q' = 0)
    (a : M ⟶ M') (b : K ⟶ K') (c : L ⟶ L')
    (hi : i ≫ b = a ≫ i') (hq : q ≫ c = b ≫ q') :
    mappingCone.map i i' a b hi ≫ cochainConeQuotient i' q' h' =
      cochainConeQuotient i q h ≫ c := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from i (n + 1) n rfl
  · simp [mappingCone.map, cochainConeQuotient]
  · simpa [mappingCone.map, cochainConeQuotient] using congrArg (fun t => t.f n) hq.symm


end SerrePositivity.KST.LocalizingInvariants

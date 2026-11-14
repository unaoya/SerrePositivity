module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexShortExactQuasiIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
概要：全射準同型な複体射の実 pullback 射影も、全射準同型となる。
方針：pullback に沿う実 kernel の同型と短完全列の長完全列を使う。
規約：非有界複体と任意の底変更。使われ方：相対経路の実射影の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L T : Complex R} (f : K ⟶ T) (g : L ⟶ T)

lemma cochainPullback_snd_epi [Epi f] : Epi (pullback.snd f g) :=
  Abelian.epi_pullback_of_epi_f f g

lemma cochainPullback_snd_quasiIso [Epi f] (hq : QuasiIso f) :
    QuasiIso (pullback.snd f g) := by
  let q := pullback.snd f g
  let sq := (IsPullback.of_hasPullback f g).flip
  let k := kernel.map q f (pullback.fst f g) g sq.w
  have : IsIso k := isIso_kernel_map_of_isPullback sq
  have : QuasiIso k := quasiIso_of_isIso k
  have hK : (kernel f).Acyclic := (cochainKernelSequence_shortExact f).acyclic_X₁ hq
  have hQ : (kernel q).Acyclic := by
    intro i
    exact (exactAt_iff_of_quasiIsoAt k i).2 (hK i)
  have : Epi q := cochainPullback_snd_epi f g
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexShortExact_quasiIso_projection (cochainKernelSequence q)
    (cochainKernelSequence_shortExact q) hQ

lemma cochainPullback_snd_surjective [Epi f] (n : ℤ) :
    Function.Surjective ((pullback.snd f g).f n) := by
  have := cochainPullback_snd_epi f g
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

lemma cochainPullback_fst_epi [Epi g] : Epi (pullback.fst f g) :=
  Abelian.epi_pullback_of_epi_g f g

lemma cochainPullback_fst_quasiIso [Epi g] (hq : QuasiIso g) :
    QuasiIso (pullback.fst f g) := by
  have h := quasiIso_comp (pullbackSymmetry f g).hom (pullback.snd g f)
    (hφ := quasiIso_of_isIso _) (hφ' := cochainPullback_snd_quasiIso g f hq)
  rw [pullbackSymmetry_hom_comp_snd] at h
  exact h

lemma cochainPullback_fst_surjective [Epi g] (n : ℤ) :
    Function.Surjective ((pullback.fst f g).f n) := by
  have := cochainPullback_fst_epi f g
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

end SerrePositivity.KST.LocalizingInvariants

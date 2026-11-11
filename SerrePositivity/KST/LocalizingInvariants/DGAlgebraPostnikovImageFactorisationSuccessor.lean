module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationLayers

/-!
概要：元の像因子分解の源射は (n+1)-connected で、標的射は新しい層で単射。
方針：証明した層の全射・単射を元の整数次数群へ移し、既存の低次数同型へ貼り合わせる。
規約：元の Perf の値の射も保持。使われ方：LT の連結なレベル表示と値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovImageFactorisationSource_groups_surjective_succ :
    Function.Surjective ((groups R (n + 1)).map (postnikovImageFactorisationSource R f n hn)).hom :=
  (ModuleCat.epi_iff_surjective _).1 (postnikovImageFactorisationSource_layer_epi R f n hn)

lemma postnikovImageFactorisationTarget_groups_injective_succ :
    Function.Injective ((groups R (n + 1)).map (postnikovImageFactorisationTarget R f n hn)).hom :=
  (ModuleCat.mono_iff_injective _).1 (postnikovImageFactorisationTarget_layer_mono R f n hn)

lemma postnikovImageFactorisationSource_connected_succ :
    IsConnected R (postnikovImageFactorisationSource R f n hn) (n + 1) := by
  refine ⟨fun j hj => (postnikovImageFactorisationSource_groups_bijective R f n hn j
    (by omega)).1, ?_⟩
  intro j hj
  by_cases h : j ≤ n
  · exact (postnikovImageFactorisationSource_groups_bijective R f n hn j h).2
  · have he : j = n + 1 := by omega
    subst j
    exact postnikovImageFactorisationSource_groups_surjective_succ R f n hn

lemma IsKConnective.postnikovImageFactorisationSource_connected_succ
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k) :
    (∀ j : ℤ, j < n + 1 + k →
      Function.Injective (invariantGroupMap R Φ (postnikovImageFactorisationSource R f n hn) j)) ∧
    ∀ j : ℤ, j ≤ n + 1 + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovImageFactorisationSource R f n hn) j) :=
  h.2 (postnikov_isConnective R B (n + 1))
    (postnikovImageFactorisationObject_isConnective R f n hn)
    (postnikovImageFactorisationSource R f n hn) (n + 1) (by omega)
    (postnikovImageFactorisationSource_groups_bijective R f n hn 0 hn)
    (DGAlgebra.postnikovImageFactorisationSource_connected_succ R f n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

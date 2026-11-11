module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageLayerFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageSourceLayer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity

/-!
概要：実関手化した源側像拡大の元の源比較は (n+1)-connected である。
方針：元の層射の全射性を整数次数群へ移し、既存の低次数同型へ貼り合わせる。
規約：実自然変換の成分と元の Perf の値の射を使用。使われ方：LT の実図式の連結度。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovSourceImageFactor_layer_epi :
    Epi (homologyMap (postnikovSourceImageFactor R f n hn).hom (-(n + 1))) := by
  apply (epi_comp_iff_of_isIso _ (postnikovSourceImageLayerHomologyIso R f n hn).hom).1
  rw [postnikovSourceImageFactor_layer]
  infer_instance

lemma postnikovSourceImageFactor_connected_succ :
    IsConnected R (postnikovSourceImageFactor R f n hn) (n + 1) := by
  refine ⟨fun j hj => (postnikovSourceImageFactor_groups_bijective R f n hn j (by omega)).1, ?_⟩
  intro j hj
  by_cases h : j ≤ n
  · exact (postnikovSourceImageFactor_groups_bijective R f n hn j h).2
  · have he : j = n + 1 := by omega
    subst j
    exact (ModuleCat.epi_iff_surjective _).1 (postnikovSourceImageFactor_layer_epi R f n hn)

lemma postnikovSourceImageArrowSource_connected (a : Arrow (NonpositiveAlgebra R)) :
    IsConnected R ((postnikovSourceImageArrowSource R n hn).app a) (n + 1) :=
  postnikovSourceImageFactor_connected_succ R a.hom.hom n hn

lemma IsKConnective.postnikovSourceImageFactor_connected_succ
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k) :
    (∀ j : ℤ, j < n + 1 + k →
      Function.Injective (invariantGroupMap R Φ (postnikovSourceImageFactor R f n hn) j)) ∧
    ∀ j : ℤ, j ≤ n + 1 + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovSourceImageFactor R f n hn) j) :=
  h.2 (postnikov_isConnective R B (n + 1)) (postnikovSourceImageExtension_isConnective R f n hn)
    (postnikovSourceImageFactor R f n hn) (n + 1) (by omega)
    (postnikovSourceImageFactor_groups_bijective R f n hn 0 hn)
    (DGAlgebra.postnikovSourceImageFactor_connected_succ R f n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

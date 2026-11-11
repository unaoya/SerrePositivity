module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantProConnectivity

/-!
概要：元の次数別 eventual 核・像条件と任意 pro 連結度を、実値の π-pro 同値へ送る。
方針：各整数次数の pro 同型を構成し、実有限切断による値の比較へ渡す。
規約：元のレベル表示・値の塔を変更しない。使われ方：LT Cor. 2.31 の弱同値の帰結。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
include h

lemma IsKConnective.invariantLevelMap_piProEquivalence_of_eventual_groups
    (hker : ∀ j : ℤ, ProGroup.IsEventuallyKernelTrivial
      ((f.map (nonpositiveInclusion R)).map (groups R j)))
    (himage : ∀ j : ℤ, ProGroup.IsEventuallyImageSurjective
      ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) :=
  h.invariantLevelMap_piProEquivalence_of_piProEquivalence R f Φ
    (fun j => ProGroup.proIso_of_kernel_image (hker j) (himage j))

lemma IsKConnective.invariantLevelMap_piProEquivalence_of_forall_proConnected
    (hf : ∀ n : ℤ, 1 ≤ n → IsPiProConnected R (f.map (nonpositiveInclusion R)) n) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) := by
  apply h.invariantLevelMap_piProEquivalence_of_piProEquivalence R f Φ
  intro j
  let n : ℤ := max 1 (j + 1)
  have hn : 1 ≤ n := le_max_left _ _
  exact IsPiProConnected.groupMap_isProIso R (hf n hn) (by
    have := le_max_right 1 (j + 1)
    omega)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor

/-!
概要：具体的 k-connective 不変量の実値関手は、connective 代数の準同型を反転する。
方針：元の BF 値の整数 π 同型で可逆性を検出し、経路の対角を可逆にする。
規約：全代数上の準同型反転を仮定しない。使われ方：実有限切断の pro 逆の値への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]


variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma IsKConnective.quasiIso_value_isIso {k : ℤ} (h : IsKConnective R Φ k)
    {B C : Mon (Complex R)} (hB : IsConnective R B) (hC : IsConnective R C)
    (f : B ⟶ C) (hf : QuasiIso f.hom) : IsIso ((invariantFunctor R Φ).map f) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism (invariantMap R Φ f)
    (fun j => h.quasiIso_bijective R Φ hB hC f hf j)

lemma IsKConnective.path_value_eq {k : ℤ} (h : IsKConnective R Φ k)
    {A B : Mon (Complex R)} (hB : IsConnective R B) {a b : A ⟶ B}
    (w : Path.Witness R a b) : (invariantFunctor R Φ).map a = (invariantFunctor R Φ).map b := by
  have := h.quasiIso_value_isIso R Φ hB (Path.isConnective hB) (Path.diagonal R B)
    (Path.diagonal_quasiIso R B)
  exact w.map_eq_of_diagonalIso R (invariantFunctor R Φ)

lemma IsKConnective.invariantFunctor_invertsConnectiveQuasiIsos
    {k : ℤ} (h : IsKConnective R Φ k) :
    InvertsConnectiveQuasiIsos R (invariantFunctor R Φ) :=
  fun hB hC f hf => h.quasiIso_value_isIso R Φ hB hC f hf

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

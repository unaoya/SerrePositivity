module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPullbackQuotientAt
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers

/-!
概要：切断商の (n+1)-連結度を、実不変量値の指定整数次数の同型へ移す。
方針：実商射と元の π₀ 同型を k-connective 条件へ渡し、BF 比較で h Sp の π に戻す。
規約：切断次数 n と値の次数 j を区別する。使われ方：実値の有限切断による近似。
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
variable (R : Type u) [CommRing R] (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})
  {k : ℤ} (h : IsKConnective R Φ k) (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (cutoff : ℤ) (hc : 0 ≤ cutoff)

include h hc

lemma IsKConnective.postnikovQuotient_pi_isIso (j : ℤ) (hj : j < cutoff + 1 + k) :
    IsIso ((SpectrumHo.piFunctor j).map
      ((invariantFunctor R Φ).map (postnikovQuotient R B cutoff))) := by
  have hv := h.2 (nonpositive_isConnective R B) (postnikov_isConnective R B cutoff)
    (postnikovQuotient R B cutoff) (cutoff + 1) (by omega)
    (postnikovQuotient_groups_bijective R B cutoff 0 hc)
    (postnikovQuotient_connected_succ R B cutoff)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨SpectrumHo.piFunctor_map_injective_of_native (invariantMap R Φ _) j (hv.1 j hj),
    SpectrumHo.piFunctor_map_surjective_of_native (invariantMap R Φ _) j (hv.2 j hj.le)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

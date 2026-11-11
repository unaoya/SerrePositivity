module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso

/-!
概要：底変更した元の隣接拡大の連結度を、元の k-connective 不変量値へ送る。
方針：実 kernel の比較で証明した連結度と、元の実 Perf・BF 射への条件を適用する。
規約：実底射を同値と仮定しない。使われ方：二切断の roof と実値の塔の接続。
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
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {P : Mon (Complex R)} [P.X.IsStrictlyLE 0] (b : P ⟶ postnikov R B n)
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma IsKConnective.postnikovExtensionBaseChangeBase_connected
    {k : ℤ} (h : IsKConnective R Φ k) (hn : 0 ≤ n) :
    (∀ j : ℤ, j < n + 1 + k → Function.Injective
      (invariantGroupMap R Φ (postnikovExtensionBaseChangeBase R B n b) j)) ∧
      ∀ j : ℤ, j ≤ n + 1 + k → Function.Surjective
        (invariantGroupMap R Φ (postnikovExtensionBaseChangeBase R B n b) j) := by
  have : (postnikovExtensionBaseChange R B n b).X.IsStrictlyLE 0 :=
    postnikovExtensionBaseChange_nonpositive R B n b
  have hU : IsConnective R (postnikovExtensionBaseChange R B n b) := by
    change (postnikovExtensionBaseChange R B n b).X.IsLE 0
    infer_instance
  have hP : IsConnective R P := by change P.X.IsLE 0; infer_instance
  exact h.2 hU hP _ (n + 1) (by omega)
    ((groups_map_bijective_iff R _ 0).2
      (postnikovExtensionBaseChangeBase_quasiIsoAt R B n b 0 (by omega)))
    (SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovExtensionBaseChangeBase_connected
      R B n b)

variable {C : Mon (Complex R)} (r : SurjectiveRoof R (postnikov R B n) C)

lemma IsKConnective.postnikovRoofBaseChangeUpper_value_isIso
    {k : ℤ} (h : IsKConnective R Φ k) (hr : r.apex.X.IsStrictlyLE 0) :
    IsIso ((invariantFunctor R Φ).map
      (postnikovExtensionBaseChangeUpper R B n r.denominator)) := by
  have : (postnikovRoofBaseChange R B n r).X.IsStrictlyLE 0 :=
    postnikovRoofBaseChange_nonpositive R B n r hr
  have hU : IsConnective R (postnikovRoofBaseChange R B n r) := by
    change (postnikovRoofBaseChange R B n r).X.IsLE 0
    infer_instance
  have hB : IsConnective R (postnikov R B (n + 1)) := by
    change (postnikov R B (n + 1)).X.IsLE 0
    have : (postnikov R B (n + 1)).X.IsStrictlyLE 0 := postnikovComplex_nonpositive R B (n + 1)
    infer_instance
  exact h.quasiIso_value_isIso R Φ hU hB _
    (postnikovRoofBaseChangeUpperInverse R B n r).denominator_quasiIso

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofKernelTransfer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangeValues

/-!
概要：共通底に移した元の二切断射と、元の実不変量値の射を両上段比較で結ぶ。
方針：元の厳密な上段合成式を実値関手に送り、両比較は元の準同型性で可逆にする。
規約：元の値・射を選び直さない。使われ方：π₂ 係数の逆と元の値の塔の接続。
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
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

lemma postnikovTwoRoofTransfer_map_upper {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) :
    L.map (postnikovTwoRoofTransfer R f c) ≫ L.map (postnikovTwoRoofDenominatorUpper R f c) =
      L.map (postnikovTwoRoofSourceUpper R f c) ≫ L.map (postnikovMap R (f.app m).hom 2) := by
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (postnikovTwoRoofTransfer_upper R f c)

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})

lemma IsKConnective.postnikovTwoRoofSourceUpper_value_isIso
    {k : ℤ} (h : IsKConnective R Φ k) :
    IsIso ((invariantFunctor R Φ).map (postnikovTwoRoofSourceUpper R f c)) := by
  have : (postnikovTwoRoofSource R f c).X.IsStrictlyLE 0 :=
    postnikovTwoRoofSource_nonpositive R f c
  have hS : IsConnective R (postnikovTwoRoofSource R f c) := by
    change (postnikovTwoRoofSource R f c).X.IsLE 0
    infer_instance
  exact h.quasiIso_value_isIso R Φ hS (postnikov_isConnective R (A.obj m).obj 2) _
    (postnikovTwoRoofSourceUpper_quasiIso R f c)

lemma IsKConnective.postnikovTwoRoofDenominatorUpper_value_isIso
    {k : ℤ} (h : IsKConnective R Φ k) :
    IsIso ((invariantFunctor R Φ).map (postnikovTwoRoofDenominatorUpper R f c)) :=
  h.postnikovRoofBaseChangeUpper_value_isIso R (B.obj m).obj 1 Φ c.roof c.roof_nonpositive

lemma postnikovTwoRoofTransfer_value_square :
    (invariantFunctor R Φ).map (postnikovTwoRoofTransfer R f c) ≫
        (invariantFunctor R Φ).map (postnikovTwoRoofDenominatorUpper R f c) =
      (invariantFunctor R Φ).map (postnikovTwoRoofSourceUpper R f c) ≫
        (invariantFunctor R Φ).map (postnikovMap R (f.app m).hom 2) :=
  postnikovTwoRoofTransfer_map_upper R f c (invariantFunctor R Φ)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

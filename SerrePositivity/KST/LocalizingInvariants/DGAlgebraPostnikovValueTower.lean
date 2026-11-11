module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantTowers
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTower
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectivity

/-!
概要：元の代数から元の Postnikov 塔への実商射を作り、不変量値の π-pro 同値を証明する。
方針：元の代数遷移と商射の厳密な式、各切断商の連結度を実値の共終判定へ送る。
規約：塔と値を実構成し、一般 pro ∞ 圏の同値とは主張しない。
使われ方：LT §2.4 の実 Postnikov 値の比較。
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
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]

/-- 元の代数の定数塔から、その元の有限 Postnikov 代数の塔への実商射。 -/
def postnikovTowerQuotient : LevelHom (Tower.constant B) (postnikovTower R B) where
  app n := postnikovQuotient R B n
  naturality {m n} h := by
    change 𝟙 B ≫ postnikovQuotient R B n =
      postnikovQuotient R B m ≫ postnikovTransition R B m n (by omega)
    rw [Category.id_comp]
    exact (postnikovQuotient_transition R B m n (by omega)).symm

lemma postnikovTowerQuotient_cofinal_connected (n : ℤ) (hn : 1 ≤ n) (i : ℕ) :
    ∃ s, ∃ _hi : i ≤ s, IsConnected R ((postnikovTowerQuotient R B).app s) n := by
  let s := max i n.toNat
  have hi : i ≤ s := le_max_left _ _
  have hs : n.toNat ≤ s := le_max_right _ _
  have hc := postnikovQuotient_connected R B (s : ℤ)
  refine ⟨s, hi, ?_, ?_⟩
  · intro j hj
    exact hc.1 j (by omega)
  · intro j hj
    exact hc.2 j (by omega)

lemma IsKConnective.postnikovTowerQuotient_piProEquivalence
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (postnikovTowerQuotient R B)) :=
  IsKConnective.invariantLevelMap_cofinal_piProEquivalence R Φ h (postnikovTowerQuotient R B)
    (fun _ => nonpositive_isConnective R B) (fun i => postnikov_isConnective R B i)
    (postnikovTowerQuotient_cofinal_connected R B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

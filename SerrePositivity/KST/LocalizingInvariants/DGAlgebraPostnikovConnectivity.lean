module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity

/-!
概要：実 Postnikov 商射の連結度を計算し、k-connective 不変量の元の値の射へ渡す。
方針：既存 H⁻ʲ 比較を代数射に戻し、具体的 IsKConnective の条件を適用する。
規約：Perf の値の射を変更しない。使われ方：有限切断から pro 版への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

lemma postnikovQuotient_groups_bijective (j : ℤ) (hj : j ≤ n) :
    Function.Bijective ((groups R j).map (postnikovQuotient R B n)).hom := by
  have := postnikovQuotient_groups_isIso R B n j hj
  exact ConcreteCategory.bijective_of_isIso _

lemma postnikovQuotient_connected : IsConnected R (postnikovQuotient R B n) n :=
  ⟨fun j hj ↦ (postnikovQuotient_groups_bijective R B n j (le_of_lt hj)).1,
    fun j hj ↦ (postnikovQuotient_groups_bijective R B n j hj).2⟩

lemma nonpositive_isConnective : IsConnective R B := by
  change B.X.IsLE 0
  infer_instance

lemma IsKConnective.postnikovQuotient_connected
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
    (hn : 1 ≤ n) :
    (∀ j : ℤ, j < n + k →
      Function.Injective (invariantGroupMap R Φ (postnikovQuotient R B n) j)) ∧
    ∀ j : ℤ, j ≤ n + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovQuotient R B n) j) :=
  h.2 (nonpositive_isConnective R B) (postnikov_isConnective R B n)
    (postnikovQuotient R B n) n hn
    (postnikovQuotient_groups_bijective R B n 0 (by omega))
    (DGAlgebra.postnikovQuotient_connected R B n)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneConnectiveInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofInvariantValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneValuePro

/-!
概要：元の一切断値の pro 逆を、Φ の選択前に構成した同じ実 dg roof で表す。
方針：元の connective roof を、具体的 IsKConnective の実値関手で評価する。
規約：値だけの逆を選び直さない。使われ方：元の値の塔と高次の底変更の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovOneMap_exists_invariantInverseRoof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
    ∃ r : SurjectiveRoof R (postnikov R (B.obj m).obj 1) (postnikov R (A.obj i).obj 1),
      ∀ (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) (k : ℤ) (h : IsKConnective R Φ k),
        (postnikovOneValueMap R Φ f).app m ≫
            h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) r =
          (invariantTower R Φ (A.map (postnikovFunctor R 1))).transition hi ∧
        h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) r ≫
            (postnikovOneValueMap R Φ f).app i =
          (invariantTower R Φ (B.map (postnikovFunctor R 1))).transition hi := by
  obtain ⟨m, hi, r, hr⟩ := postnikovOneMap_hasConnectiveRoofProInverse R f
    (D := hoFunctor.obj Sp.{u + 1}) h₀ h₁ i
  refine ⟨m, hi, r, ?_⟩
  intro Φ k h
  exact hr (invariantFunctor R Φ) (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)

lemma nonpositiveMap_exists_invariantInverseRoof_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (B.obj m).obj (A.obj i).obj,
      ∀ (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) (k : ℤ) (h : IsKConnective R Φ k),
        (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))).app m ≫
            h.roofValue R Φ (nonpositive_isConnective R (B.obj m).obj) r =
          (invariantTower R Φ (A.map (nonpositiveInclusion R))).transition hi ∧
        h.roofValue R Φ (nonpositive_isConnective R (B.obj m).obj) r ≫
            (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))).app i =
          (invariantTower R Φ (B.map (nonpositiveInclusion R))).transition hi := by
  obtain ⟨m, hi, r, hr⟩ := nonpositiveMap_hasConnectiveRoofProInverse_of_oneBounded R f
    (D := hoFunctor.obj Sp.{u + 1}) hA hB h₀ h₁ i
  refine ⟨m, hi, r, ?_⟩
  intro Φ k h
  exact hr (invariantFunctor R Φ) (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

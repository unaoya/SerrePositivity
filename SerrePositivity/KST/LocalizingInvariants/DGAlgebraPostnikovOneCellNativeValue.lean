module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneCellNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofInvariantValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneValuePro

/-!
概要：元の一切断射の実三角形付き roof 逆を、Φ を選ぶ前に構成して値へ送る。
方針：同じ実 cell 持ち上げ・右経路を持つ roof を元の実不変量関手で評価する。
規約：評価後に別の逆を選ばない。使われ方：高次底変更と元の実値の塔の接続。
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

lemma postnikovOneMap_exists_cellNativeInvariantInverseRoof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, ∃ c : CellNativeInverseRoof R (f.map (postnikovFunctor R 1)) i m hi,
      ∀ (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) (k : ℤ) (h : IsKConnective R Φ k),
        (postnikovOneValueMap R Φ f).app m ≫
            h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) c.roof =
          (invariantTower R Φ (A.map (postnikovFunctor R 1))).transition hi ∧
        h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) c.roof ≫
            (postnikovOneValueMap R Φ f).app i =
          (invariantTower R Φ (B.map (postnikovFunctor R 1))).transition hi := by
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovOneMap_hasCellNativeRoofProInverse R f h₀ h₁ i
  refine ⟨m, hi, c, ?_⟩
  intro Φ k h
  exact c.connectiveValue_triangles R (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)
    (postnikov_isConnective R (A.obj m).obj 1)
    (postnikov_isConnective R (B.obj m).obj 1) (postnikov_isConnective R (B.obj i).obj 1)

lemma nonpositiveMap_exists_cellNativeInvariantInverseRoof_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, ∃ c : CellNativeInverseRoof R (f.map (nonpositiveInclusion R)) i m hi,
      ∀ (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) (k : ℤ) (h : IsKConnective R Φ k),
        (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))).app m ≫
            h.roofValue R Φ (nonpositive_isConnective R (B.obj m).obj) c.roof =
          (invariantTower R Φ (A.map (nonpositiveInclusion R))).transition hi ∧
        h.roofValue R Φ (nonpositive_isConnective R (B.obj m).obj) c.roof ≫
            (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))).app i =
          (invariantTower R Φ (B.map (nonpositiveInclusion R))).transition hi := by
  obtain ⟨m, hi, ⟨c⟩⟩ :=
    nonpositiveMap_hasCellNativeRoofProInverse_of_oneBounded R f hA hB h₀ h₁ i
  refine ⟨m, hi, c, ?_⟩
  intro Φ k h
  exact c.connectiveValue_triangles R (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)
    (nonpositive_isConnective R (A.obj m).obj) (nonpositive_isConnective R (B.obj m).obj)
    (nonpositive_isConnective R (B.obj i).obj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

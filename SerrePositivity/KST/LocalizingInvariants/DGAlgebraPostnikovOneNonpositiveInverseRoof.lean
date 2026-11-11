module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneCellNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofInvariantValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneValuePro

/-!
概要：元の一切断射の逆を、全頂点が非正次数の実三角形付き roof として構成する。
方針：構成済みの cell 三角形付き逆を同じ connective cover で正規化し、値へ送る。
規約：元の両脚・経路・実値の三角形を保持。使われ方：二切断の class の底変更。
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

lemma postnikovOneMap_exists_nonpositiveInverseRoof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, Nonempty (NonpositiveInverseRoof R
      (f.map (postnikovFunctor R 1)) i m hi) := by
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovOneMap_hasCellNativeRoofProInverse R f h₀ h₁ i
  have : ((A.map (postnikovFunctor R 1)).obj m).X.IsStrictlyLE 0 := by
    change (postnikov R (A.obj m).obj 1).X.IsStrictlyLE 0
    infer_instance
  have : ((B.map (postnikovFunctor R 1)).obj m).X.IsStrictlyLE 0 := by
    change (postnikov R (B.obj m).obj 1).X.IsStrictlyLE 0
    infer_instance
  exact ⟨m, hi, ⟨c.nonpositive R⟩⟩

lemma nonpositiveMap_exists_nonpositiveInverseRoof_of_oneBounded
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-1)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-1))
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, Nonempty (NonpositiveInverseRoof R
      (f.map (nonpositiveInclusion R)) i m hi) := by
  obtain ⟨m, hi, ⟨c⟩⟩ :=
    nonpositiveMap_hasCellNativeRoofProInverse_of_oneBounded R f hA hB h₀ h₁ i
  have : ((A.map (nonpositiveInclusion R)).obj m).X.IsStrictlyLE 0 := by
    change (A.obj m).obj.X.IsStrictlyLE 0
    infer_instance
  have : ((B.map (nonpositiveInclusion R)).obj m).X.IsStrictlyLE 0 := by
    change (B.obj m).obj.X.IsStrictlyLE 0
    infer_instance
  exact ⟨m, hi, ⟨c.nonpositive R⟩⟩

lemma postnikovOneMap_exists_nonpositiveInvariantInverseRoof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
    ∃ c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi,
      ∀ (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) (k : ℤ) (h : IsKConnective R Φ k),
        (postnikovOneValueMap R Φ f).app m ≫
            h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) c.roof =
          (invariantTower R Φ (A.map (postnikovFunctor R 1))).transition hi ∧
        h.roofValue R Φ (postnikov_isConnective R (B.obj m).obj 1) c.roof ≫
            (postnikovOneValueMap R Φ f).app i =
          (invariantTower R Φ (B.map (postnikovFunctor R 1))).transition hi := by
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovOneMap_exists_nonpositiveInverseRoof R f h₀ h₁ i
  refine ⟨m, hi, c, ?_⟩
  intro Φ k h
  exact c.connectiveValue_triangles R (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)
    (postnikov_isConnective R (A.obj m).obj 1) (postnikov_isConnective R (B.obj m).obj 1)
    (postnikov_isConnective R (B.obj i).obj 1)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

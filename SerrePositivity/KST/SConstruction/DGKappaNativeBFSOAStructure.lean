module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOAAdjoint
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOAZeroStructure
public import SerrePositivity.KST.SConstruction.PointedComponentAdjointSquare

/-! # 元の旧 BF 列と新 BF 列の全構造射の点つき比較
概要：全段の前向き弱比較は、零段を含む全構造射と点つき成分で可換。
方針：全正随伴比較を uncurry し、旧単射置換の厳密射影と合成する。
規約：実スペクトル射への修正は別工程。使われ方：元の K との実比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open DifferentialGraded NonConnective Fibration
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：全正構造射は、元の前向き段比較で点つき成分が可換。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFRawSOAComparison_positive_structure (r : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 1) ≫
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma (r + 1)) =
      componentOf (boundaryKanAssemblySigma r
          (sInputModel C.obj) ≫
        dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 2)) := by
  exact pointedComponentAdjointSquare
    (dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 1))
    (dgKappaNativeBFRawSOAComparison.{u, v} R D I C (r + 2))
    (boundaryKanAssemblyAdjoint r
      (sInputModel C.obj))
    ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma (r + 1))
    (dgKappaNativeBFRawSOAComparison_positive_adjoint.{u, v} R D I r C)

/-- 概要：元の K 候補列からの比較は零段を含む全構造射と点つき成分で可換。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFRawSOAComparison_structure
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        dgKappaNativeBFRawSOAComparison.{u, v} R D I C n ≫
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma n) =
      componentOf
        ((kKanSequence (sInputModel C.obj)).sigma n ≫
          dgKappaNativeBFRawSOAComparison.{u, v} R D I C (n + 1)) := by
  cases n with
  | zero => exact dgKappaNativeBFRawSOAComparison_zero_structure.{u, v} R D I C
  | succ r => exact dgKappaNativeBFRawSOAComparison_positive_structure.{u, v} R D I r C

/-- 概要：同じ旧単射 BF K からの全段比較も、全構造射と点つき成分で可換。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOAComparison_structure
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        dgKappaNativeBFSOAComparison.{u, v} R D I C n ≫
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma n) =
      componentOf
        ((kOmegaSpectrum (sInputModel C.obj)).sigma n ≫
          dgKappaNativeBFSOAComparison.{u, v} R D I C (n + 1)) := by
  let p := monicKKanSequenceProjection
    (sInputModel C.obj)
  have h := componentOf_comp_left (dgKappaNativeBFRawSOAComparison_structure.{u, v} R D I C n)
    (PointedSimplicialSet.circle.{max (u + 1) v} ◁ p.app n)
  change componentOf ((PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (p.app n ≫ dgKappaNativeBFRawSOAComparison.{u, v} R D I C n)) ≫ _) =
      componentOf (_ ≫ (p.app (n + 1) ≫ dgKappaNativeBFRawSOAComparison.{u, v} R D I C (n + 1)))
  erw [whiskerLeft_comp]
  have hp := congrArg (fun f => componentOf
    (f ≫ dgKappaNativeBFRawSOAComparison.{u, v} R D I C (n + 1))) (p.comm n)
  simp only [Category.assoc] at h hp ⊢
  exact h.trans hp

end SerrePositivity.KST.SConstruction

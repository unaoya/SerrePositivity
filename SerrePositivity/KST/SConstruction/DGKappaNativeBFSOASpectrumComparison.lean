module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOAStructure
public import SerrePositivity.KST.Spectra.SequenceHomotopyRectification
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-! # 元の SOA K から新 BF K への実スペクトル比較
概要：全構造射の点つき成分比較を、同じ両対象間の厳密 BF 射へ修正する。
方針：既存の単射構造射に沿う点ごとの修正を適用し、各段の元の弱比較を保持する。
規約：入力全体の豊穣作用は選び直さない。使われ方：元の K との実弱同値比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open DifferentialGraded NonConnective Fibration
open CategoryTheory SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ旧単射 K 列から新 BF 列への、構造射と厳密に可換な実比較。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFSOASequenceComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanSequence.Hom
      (kOmegaSpectrum (sInputModel C.obj)).toKanSequence
      (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).toKanSequence :=
  KanSequence.rectify
    (kOmegaSpectrum (sInputModel C.obj)).sigma_mono
    (dgKappaNativeBFSOAComparison.{u, v} R D I C)
    (dgKappaNativeBFSOAComparison_structure.{u, v} R D I C)

/-- 概要：同じ旧 SOA BF K から新 BF K への実際の厳密スペクトル射。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFSOASpectrumComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    kOmegaSpectrum (sInputModel C.obj) ⟶
      dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C where
  app := (dgKappaNativeBFSOASequenceComparison.{u, v} R D I C).app
  comm := (dgKappaNativeBFSOASequenceComparison.{u, v} R D I C).comm

/-- 概要：同じ実スペクトル比較は、全段で元の前向き弱比較の点つき成分を保つ。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOASpectrumComparison_component
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    componentOf ((dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C).app n) =
      componentOf (dgKappaNativeBFSOAComparison.{u, v} R D I C n) :=
  KanSequence.rectify_component _ _ _ n

/-- 概要：同じ実スペクトル比較は、零段を含む全段で全基点 π 同型。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOASpectrumComparison_levelwise
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C).app n).right :=
  KanSequence.rectify_levelwise _ _ _ (dgKappaNativeBFSOAComparison_piIsomorphism.{u, v} R D I C) n

/-- 概要：同じ実 BF 比較射は全整数次数で π 同型。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOASpectrumComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    OmegaSpectrum.PiIsomorphism (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (dgKappaNativeBFSOASpectrumComparison_levelwise.{u, v} R D I C)

/-- 概要：同じ実スペクトル比較の零段は、元の二 Kan 模型の loop 比較を保つ。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOASpectrumComparison_zero (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFSOASpectrumComparison.{u, v} R D I C).app 0 =
      dgKappaNativeBFSOAComparison.{u, v} R D I C 0 := rfl

end SerrePositivity.KST.SConstruction

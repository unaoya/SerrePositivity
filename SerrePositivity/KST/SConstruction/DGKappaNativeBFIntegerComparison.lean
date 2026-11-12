module
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFSquare
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
概要：同じ native 四頂点像の実 BF 値を旧 K の全整数群へ接続する。
方針：常に正段にある標準表示で、元の射影・Ex∞ 比較・実帰納比較を合成する。
規約：全 Sp 写像空間での旧辺比較を要求しない。使われ方：K-B・K-cof の整数群接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open Fibration
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：旧 BF 正段から同じ実 BF 正段への指定点つき比較。
方針：元 SOA 射影と Ex∞ 比較の後に、同じ実再帰比較を合成する。
規約：同じ四頂点像に限定。使われ方：全整数群同型の順写像。 -/
def dgKappaNativeBFPositiveLevelComparison
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (r : ℕ) :
    ((kOmegaSpectrum (sInputModel C.obj)).level (r + 1)).space ⟶
      ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).level (r + 1)).space :=
  (monicKKanSequenceProjection (sInputModel C.obj)).app (r + 1) ≫
    pointedSOAExInfinityComparison (stableBoundaryPointedObject r C.obj) ≫
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C

/-- 概要：同じ指定正段比較は全基点 π 同型。
方針：元射影・Ex∞ 比較・同じ帰納比較の π 同型性を合成する。
規約：全正段で証明。使われ方：全整数の指定群同型。 -/
lemma dgKappaNativeBFPositiveLevelComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C r).right :=
  (monicKKanSequenceProjection_piIsomorphism (sInputModel C.obj) (r + 1)).comp
    ((pointedSOAExInfinityComparison_piIsomorphism (stableBoundaryPointedObject r C.obj)).comp
      (dgKappaNativeBFFiniteStageComparison_piIsomorphism.{u, v} R D I r
        (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r) C))

/-- 概要：同じ正段比較が誘導する全整数群の指定準同型。
方針：次数 j の標準段 |j|+1 の正次数写像を使う。
規約：零次数・負次数も含む。使われ方：新旧四辺の整数群自然性。 -/
def dgKappaNativeBFIntegerComparison
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel C.obj)) j →*
      OmegaSpectrum.homotopyGroup (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C) j :=
  OmegaSpectrum.positiveLevelMap _ _ (OmegaSpectrum.canonicalLevel j)
    (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j)) (OmegaSpectrum.canonicalDegree_pos j)
    (dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C j.natAbs)

/-- 概要：指定整数群準同型の全単射性。
方針：同じ正段比較の全基点 π 同型を標準段で使う。
規約：任意の整数次数。使われ方：指定群同型の構成。 -/
lemma dgKappaNativeBFIntegerComparison_bijective
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (j : ℤ) :
    Function.Bijective (dgKappaNativeBFIntegerComparison.{u, v} R D I C j) := by
  let c := dgKappaNativeBFPositiveLevelComparison.{u, v} R D I C j.natAbs
  have h : (fun a => dgKappaNativeBFIntegerComparison.{u, v} R D I C j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism
        (OmegaSpectrum.degree j (OmegaSpectrum.canonicalLevel j)) c.right
        (dgKappaNativeBFPositiveLevelComparison_piIsomorphism.{u, v} R D I C j.natAbs)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint c) := by
    funext a
    exact (OmegaSpectrum.positiveLevelMap_apply _ _ _ _ _ c a).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply _ _ _ _ a).symm
  change Function.Bijective (fun a => dgKappaNativeBFIntegerComparison.{u, v} R D I C j a)
  rw [h]
  exact Equiv.bijective _

/-- 概要：旧 K と同じ実 BF 値の全整数群の指定同型。
方針：同じ前向き準同型を全単射性で束ねる。
規約：順写像を選び直さない。使われ方：新四辺と旧 K の π 作用の可換性。 -/
def dgKappaNativeBFIntegerComparisonEquiv
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel C.obj)) j ≃*
      OmegaSpectrum.homotopyGroup (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C) j :=
  MulEquiv.ofBijective (dgKappaNativeBFIntegerComparison.{u, v} R D I C j)
    (dgKappaNativeBFIntegerComparison_bijective.{u, v} R D I C j)

end SerrePositivity.KST.SConstruction

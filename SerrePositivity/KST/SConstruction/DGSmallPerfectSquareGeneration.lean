module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareQuotientEnd
public import SerrePositivity.KST.SConstruction.DGGeneratorImagePerfect
public import SerrePositivity.KST.SConstruction.DGGluingDiagonalQuotientPoint
public import SerrePositivity.KST.SConstruction.DGEndInclusionPerfectGeneration
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence

/-! # 元の実比較対角の自由代表による生成と End 包含の Morita 判定
概要：元の二つの実自由代表の生成条件から、同じ実比較対角の商 End 包含を判定する。
方針：元の左実延長の代表比較で左像生成を供給し、既存の実二軸と D の商零化を使う。
規約：実自由代表の生成条件は未供給の明示入力。使われ方：D の実生成 API の接続先。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q)
local notation "CL" => DGSmallPerfectArrowTarget R P C L
local notation "DR" => DGSmallPerfectArrowTarget R P D G
local notation "V" => DGSmallPerfectSquareCorner R P C D E L G p q
local notation "pS" => dgSmallPerfectSquareLeftMap R P C D E L G p q
local notation "qS" => dgSmallPerfectSquareRightMap R P C D E L G p q
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "j" => dgSmallPerfectSquareDiagonal R P C D E L G p q h
local notation "zc" => dgSmallPerfectArrowTargetZero R P C L
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R P C L
local notation "zd" => dgSmallPerfectArrowTargetZero R P D G
local notation "hd" => dgSmallPerfectArrowTargetZero_isZero R P D G

/-- 左の実自由代表が生成すれば、元の比較対角の左成分像が全 Perf を生成する。 -/
lemma dgSmallPerfectSquareDiagonal_left_generates (a : P)
    (hC : modulePerfectOver R (CL)
      {dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)} = modulePerfect R (CL)) :
    modulePerfectOver R (CL) (Set.range (fun x => ((j).obj x).left)) = modulePerfect R (CL) :=
  dgPerfectOver_image_eq_of_generator_iso R (CL) (dgSmallPerfectArrow R P C L)
    (dgSmallPerfectBaseRepresentable R P a)
    (dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)) hC
    ((toHomotopy R (CL)).mapIso (dgSmallPerfectArrowRepresentableIso R P C L a))

variable (b : D)
local notation "I" => dgSmallPerfectSquareQuotientInput R P C D E L G p q h b
local notation "br" => dgSmallPerfectArrowTargetRepresentable R P D G b
/-- 元の二つの実自由代表の生成条件から、同じ実比較対角商の指定対象が生成する。 -/
lemma dgSmallPerfectSquareQuotient_perfectOver_point_eq (a : P)
    (hC : modulePerfectOver R (CL)
      {dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)} = modulePerfect R (CL))
    (hD : modulePerfectOver R (DR) {(br)} = modulePerfect R (DR)) :
    modulePerfectOver R (I).quotientObject {(I).projection.obj (I).point} =
      modulePerfect R (I).quotientObject :=
  dgGluingDiagonalQuotient_perfectOver_point_eq R (CL) (DR) (M) (zc) (hc) (zd) (hd) (j) (br)
    (dgSmallPerfectSquareDiagonal_left_generates R P C D E L G p q h a hC) hD

/-- 同じ元の実自由代表の生成条件下で、元の指定 End 包含の実 Perf 延長が圏同値。 -/
lemma dgSmallPerfectSquareEndInclusion_isMorita (a : P)
    (hC : modulePerfectOver R (CL)
      {dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)} = modulePerfect R (CL))
    (hD : modulePerfectOver R (DR) {(br)} = modulePerfect R (DR)) :
    (quasiEquivalencePerfectExtension R (I).endObject (I).quotientObject
      (I).endInclusion).IsEquivalence :=
  dgEndInclusionPerfect_isEquivalence R (I).quotientObject ((I).projection.obj (I).point)
    (dgSmallPerfectSquareQuotient_perfectOver_point_eq R P C D E L G p q h b a hC hD)

/-- 元の指定 End 包含の実 dg Perf 延長も、同じ生成条件下で準同値。 -/
lemma dgSmallPerfectSquareEndInclusion_perfectDG_quasiEquivalence (a : P)
    (hC : modulePerfectOver R (CL)
      {dgSmallPerfectArrowTargetRepresentable R P C L (L.obj a)} = modulePerfect R (CL))
    (hD : modulePerfectOver R (DR) {(br)} = modulePerfect R (DR)) :
    QuasiEquivalence (perfectDGExtension R (I).endObject (I).quotientObject (I).endInclusion) := by
  let := dgSmallPerfectSquareEndInclusion_isMorita R P C D E L G p q h b a hC hD
  exact perfectDGExtension_quasiEquivalence R (I).endObject (I).quotientObject (I).endInclusion

end SerrePositivity.KST.SConstruction

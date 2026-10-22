module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareDiagonal
public import SerrePositivity.KST.SConstruction.DGSmallPerfectArrowObjects
public import SerrePositivity.KST.SConstruction.DGLaxQuotientEnd

/-! # 元の実 Perf 比較を持つ小模型対角の指定商 End
概要：元の比較を持つ実対角と実零左成分・実代表右成分から、同じ対角商 End を作る。
方針：既存の具体的商 End 入力に元の対象と比較を渡す。
規約：商 API は D の正本を使う。使われ方：実 LT 入力の具体的な ⊙ 模型。
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
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q) (b : D)
local notation "CL" => DGSmallPerfectArrowTarget R P C L
local notation "DR" => DGSmallPerfectArrowTarget R P D G
local notation "V" => DGSmallPerfectSquareCorner R P C D E L G p q
local notation "pS" => dgSmallPerfectSquareLeftMap R P C D E L G p q
local notation "qS" => dgSmallPerfectSquareRightMap R P C D E L G p q

/-- 元の実対角・実零加群・実右代表を保持する、同じ具体的商 End 入力。 -/
def dgSmallPerfectSquareQuotientInput :
    DGLaxQuotientEndInput R (CL) (DR) (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS))
      (DGSmallPerfectBase R P) :=
  DGLaxQuotientEndInput.ofClosedZero (dgSmallPerfectSquareDiagonal R P C D E L G p q h)
    (dgSmallPerfectArrowTargetZero R P C L) (dgSmallPerfectArrowTargetZero_isZero R P C L)
    (dgSmallPerfectArrowTargetRepresentable R P D G b)

/-- 元の実 Perf 比較の対角像を消した商内の、同じ指定右代表の全 dg End。 -/
abbrev dgSmallPerfectSquareQuotientEnd :=
  (dgSmallPerfectSquareQuotientInput R P C D E L G p q h b).endObject

end SerrePositivity.KST.SConstruction

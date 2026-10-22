module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareQuotientEnd
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeYoneda
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisEnd
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence

/-! # 元の右対象 End から実 Perf 比較の対角商 End への射
概要：元の右 dg 対象の全 End を、同じ実代表・右軸・対角商の指定 End へ送る。
方針：小模型への厳密 Yoneda と元の右軸商 End 射を合成する。
規約：元の対象・零成分・比較を保持。使われ方：具体的 ⊙ への元の右端の射。
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
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "j" => dgSmallPerfectSquareDiagonal R P C D E L G p q h
local notation "I" => dgSmallPerfectSquareQuotientInput R P C D E L G p q h b
local notation "zc" => dgSmallPerfectArrowTargetZero R P C L
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R P C L
local notation "br" => dgSmallPerfectArrowTargetRepresentable R P D G b
local notation "Y" => dgSmallPerfectEnvelopeYoneda R D (DGSmallPerfectBase R P)
  (dgSmallPerfectEnvelopeExtensionFamily R P D Empty (dgSmallPerfectBaseFamily R P) G)
local notation "F₀" => endomorphismMap R (Y) b
local notation "F₁" => dgGluingRightQuotientEndMap R (CL) (DR) (M) (zc) (hc) (j) (br)
local notation "A" => dgGluingRightAxis R (CL) (DR) (M) (zc) (hc)

/-- 元の右対象の全 dg End から、元の実 Perf 比較対角の指定商 End への実射。 -/
def dgSmallPerfectSquareRightEndMap : DGFunctor R (EndomorphismObject b) (I).endObject :=
  (F₀).comp (F₁)

/-- 同じ End 射の商への包含は、元の厳密 Yoneda・右軸・商射の合成を回収する。 -/
lemma dgSmallPerfectSquareRightEndMap_inclusion :
    (dgSmallPerfectSquareRightEndMap R P C D E L G p q h b).comp (I).endInclusion =
    (((endomorphismInclusion R b).comp (Y)).comp (A)).comp (I).projection := by
  change ((F₀).comp (F₁)).comp (I).endInclusion = _
  calc
    ((F₀).comp (F₁)).comp (I).endInclusion = (F₀).comp ((F₁).comp (I).endInclusion) :=
      strictDGFunctor_comp_assoc _ _ _
    _ = (F₀).comp (((endomorphismInclusion R (br)).comp (A)).comp (I).projection) :=
      congrArg (DGFunctor.comp (F₀))
        (dgGluingRightQuotientEndMap_inclusion R (CL) (DR) (M) (zc) (hc) (j) (br))
    _ = (((F₀).comp (endomorphismInclusion R (br))).comp (A)).comp (I).projection := by
      exact (strictDGFunctor_comp_assoc (F₀)
        ((endomorphismInclusion R (br)).comp (A)) (I).projection).symm.trans
          (congrArg (fun T => T.comp (I).projection)
            (strictDGFunctor_comp_assoc (F₀) (endomorphismInclusion R (br)) (A)).symm)
    _ = _ := congrArg (fun T => (T.comp (A)).comp (I).projection)
      (endomorphismMap_comp_inclusion R (Y) b)

end SerrePositivity.KST.SConstruction

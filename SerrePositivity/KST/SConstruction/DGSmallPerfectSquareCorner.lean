module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectArrow

/-! # 二つの実延長像を含む共通終域の小さい Perf 模型
概要：元の左右小模型の実像族の和を使い、二辺に共通の終域を固定する。
方針：和型で添字付けた実延長像を既存の小模型へ加える。
規約：四角形の比較は次工程。使われ方：元の実四角形の共通終域。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "CL" => DGSmallPerfectArrowTarget R P C L
local notation "DR" => DGSmallPerfectArrowTarget R P D G

/-- 元の左右両小模型の実延長像を、同じ和型で添字付ける。 -/
def dgSmallPerfectSquareCornerFamily : (CL) ⊕ (DR) → PerfectDGModule R E
  | .inl x => (perfectDGExtension R C E p).obj x.val
  | .inr y => (perfectDGExtension R D E q).obj y.val

/-- 元の左右二辺の実延長像を同時に含む、共通終域の実小模型。 -/
abbrev DGSmallPerfectSquareCorner :=
  DGSmallPerfectEnvelope R E ((CL) ⊕ (DR)) (dgSmallPerfectSquareCornerFamily R P C D E L G p q)

/-- 元の左右の小ささから、同じ共通終域の実対象集合の小ささを得る。 -/
instance dgSmallPerfectSquareCornerSmall :
    Small.{u} (DGSmallPerfectSquareCorner R P C D E L G p q) :=
  dgSmallPerfectEnvelopeSmall R E ((CL) ⊕ (DR))
    (dgSmallPerfectSquareCornerFamily R P C D E L G p q)

/-- 同じ共通終域から元の全 Perf への、全 Hom を保つ包含。 -/
def dgSmallPerfectSquareCornerInclusion :
    DGFunctor R (DGSmallPerfectSquareCorner R P C D E L G p q) (PerfectDGModule R E) :=
  dgSmallPerfectEnvelopeInclusion R E ((CL) ⊕ (DR))
    (dgSmallPerfectSquareCornerFamily R P C D E L G p q)

end SerrePositivity.KST.SConstruction

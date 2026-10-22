module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareCorner

/-! # 元の二辺の共通小終域への厳密な実延長
概要：左右両小模型から共通終域へ、元の実延長を対象と全 Hom を保って制限する。
方針：和型の左右ラベルを指定実像の所属証明に使い、D の充満部分圏制限を適用する。
規約：実延長の合成を等号と仮定しない。使われ方：元の実四角形の比較対角。
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
local notation "V" => DGSmallPerfectSquareCorner R P C D E L G p q
local notation "OC" => dgSmallPerfectEnvelopeObjects R C (DGSmallPerfectBase R P)
  (dgSmallPerfectEnvelopeExtensionFamily R P C Empty (dgSmallPerfectBaseFamily R P) L)
local notation "OD" => dgSmallPerfectEnvelopeObjects R D (DGSmallPerfectBase R P)
  (dgSmallPerfectEnvelopeExtensionFamily R P D Empty (dgSmallPerfectBaseFamily R P) G)
local notation "OE" => dgSmallPerfectEnvelopeObjects R E ((CL) ⊕ (DR))
  (dgSmallPerfectSquareCornerFamily R P C D E L G p q)

/-- 左からの元の実延長を、同じ実像を含む共通終域へ厳密に制限する。 -/
def dgSmallPerfectSquareLeftMap : DGFunctor R (CL) (V) :=
  (perfectDGExtension R C E p).restrict (OC) (OE)
    (fun a ha => Or.inr (Or.inl ⟨Sum.inl ⟨a, ha⟩, rfl⟩))

/-- 右からの元の実延長を、同じ実像を含む共通終域へ厳密に制限する。 -/
def dgSmallPerfectSquareRightMap : DGFunctor R (DR) (V) :=
  (perfectDGExtension R D E q).restrict (OD) (OE)
    (fun a ha => Or.inr (Or.inl ⟨Sum.inr ⟨a, ha⟩, rfl⟩))

/-- 左の制限は、共通終域への包含後に元の実延長を全 Hom で厳密に回収する。 -/
lemma dgSmallPerfectSquareLeftMap_inclusion :
    (dgSmallPerfectSquareLeftMap R P C D E L G p q).comp
      (dgSmallPerfectSquareCornerInclusion R P C D E L G p q) =
    (dgSmallPerfectArrowTargetInclusion R P C L).comp (perfectDGExtension R C E p) :=
  DGFunctor.restrict_comp_inclusion (perfectDGExtension R C E p) (OC) (OE)
    (fun a ha => Or.inr (Or.inl ⟨Sum.inl ⟨a, ha⟩, rfl⟩))

/-- 右の制限も、共通終域への包含後に元の実延長を全 Hom で厳密に回収する。 -/
lemma dgSmallPerfectSquareRightMap_inclusion :
    (dgSmallPerfectSquareRightMap R P C D E L G p q).comp
      (dgSmallPerfectSquareCornerInclusion R P C D E L G p q) =
    (dgSmallPerfectArrowTargetInclusion R P D G).comp (perfectDGExtension R D E q) :=
  DGFunctor.restrict_comp_inclusion (perfectDGExtension R D E q) (OD) (OE)
    (fun a ha => Or.inr (Or.inl ⟨Sum.inr ⟨a, ha⟩, rfl⟩))

end SerrePositivity.KST.SConstruction

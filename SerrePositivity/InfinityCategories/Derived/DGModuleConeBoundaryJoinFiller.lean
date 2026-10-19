module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundarySimplices

/-! # 左右の単体を貼り合わせた join の充填

概要：共通面で一致する左右の実際の単体を標準 span の join 上の一つの写像へ貼る。
方針：二セル表示の押し出しの普遍性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：coslice の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：左右の単体を表す写像は押し出しの共通面で一致する。
方針：面の Yoneda 公式で単体の共通面の等式へ戻す。
規約：HTT §1.2.13。使われ方：join の二セルの貼合せの整合条件。 -/
lemma dgModuleConeBoundaryCells_compatible {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    SSet.stdSimplex.δ (spanJoinCommonFace (n + 1)) ≫
        (SSet.yonedaEquiv.symm (dgModuleConeBoundaryLeftSimplex A D f b hb) :
          (Δ[n + 3] : SSet) ⟶ dgModuleNerve A D) =
      SSet.stdSimplex.δ (spanJoinCommonFace (n + 1)) ≫
        SSet.yonedaEquiv.symm (dgModuleConeBoundaryRightSimplex A D f b hb) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  exact dgModuleConeBoundarySimplex_common A D f b hb

/-- 概要：左右の単体を標準 span の join 上の一写像に貼り合わせる。
方針：二つの標準セルの押し出しに、共通面で一致する二写像を与える。
規約：HTT §1.2.13。使われ方：実際の slice の充填写像の uncurry。 -/
def dgModuleConeBoundaryJoinFiller {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    join (SSet.horn 2 0 : SSet) Δ[n + 1] ⟶ dgModuleNerve A D :=
  (spanJoin_isPushout (n + 1)).desc
    (SSet.yonedaEquiv.symm (dgModuleConeBoundaryLeftSimplex A D f b hb))
    (SSet.yonedaEquiv.symm (dgModuleConeBoundaryRightSimplex A D f b hb))
    (dgModuleConeBoundaryCells_compatible A D f b hb)

/-- 概要：貼合せた充填の左セルへの制限は構成した左単体。
方針：押し出しの降下の第一の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の左の既知面との比較。 -/
lemma dgModuleConeBoundaryJoinFiller_left {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    spanJoinLeft (n + 1) ≫ dgModuleConeBoundaryJoinFiller A D f b hb =
      SSet.yonedaEquiv.symm (dgModuleConeBoundaryLeftSimplex A D f b hb) :=
  (spanJoin_isPushout (n + 1)).inl_desc _ _ _

/-- 概要：貼合せた充填の右セルへの制限は構成した右単体。
方針：押し出しの降下の第二の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の右の既知面との比較。 -/
lemma dgModuleConeBoundaryJoinFiller_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    spanJoinRight (n + 1) ≫ dgModuleConeBoundaryJoinFiller A D f b hb =
      SSet.yonedaEquiv.symm (dgModuleConeBoundaryRightSimplex A D f b hb) :=
  (spanJoin_isPushout (n + 1)).inr_desc _ _ _

end SerrePositivity.InfinityCategories

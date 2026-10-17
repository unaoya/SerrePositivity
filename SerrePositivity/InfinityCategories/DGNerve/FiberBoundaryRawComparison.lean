module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundarySharedResiduals
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryUnknownZero

/-! # 型付き残差と生データの異種等号による比較

概要：型付きの各右辺を回収した生の右辺と比較し、基底データの既知方程式と零性を記録する。
方針：移送前後の異種等号と零未知データの既存の回収定理を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：生の Bianchi を型付きの整合式へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：型付きの r_0 は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhs0_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhs0 g h b hb) ((fiberBoundaryLeftBase g h b).cospanPrefixRhs) := by
  unfold fiberBoundaryRhs0
  apply gradedHomTransport_heq_of_heq (A := A) (D := Complex A)
  exact HEq.rfl

/-- 概要：型付きの r_B は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhsB_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhsB g h b hb) ((fiberBoundaryLeftBase g h b).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)) := by
  unfold fiberBoundaryRhsB
  apply gradedHomTransport_heq_of_heq (A := A) (D := Complex A)
  exact HEq.rfl

/-- 概要：型付きの r_C は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhsC_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhsC g h b hb) ((fiberBoundaryRightBase g h b).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)) :=
  (fiberBoundaryRhsCWithHEq g h b hb).property

/-- 概要：型付きの r_D は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhsD_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhsD g h b hb) ((fiberBoundaryLeftBase g h b).cospanOneTailRhs
      (cospanLastTail n)
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))) := by
  unfold fiberBoundaryRhsD
  apply gradedHomTransport_heq_of_heq (A := A) (D := Complex A)
  exact HEq.rfl

/-- 概要：型付きの r_BD は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhsBD_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhsBD g h b hb) ((fiberBoundaryLeftBase g h b).cospanTwoTailRhs) := by
  unfold fiberBoundaryRhsBD
  apply gradedHomTransport_heq_of_heq (A := A) (D := Complex A)
  exact HEq.rfl

/-- 概要：型付きの r_CD は対応する生の右辺と異種等号で一致する。
方針：Hom の移送が元の射と異種等号で一致することを使う。
規約：HTT §1.2.13。使われ方：微分・合成の式を固定した Hom の式へ変換する。 -/
lemma fiberBoundaryRhsCD_heq_raw {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq (fiberBoundaryRhsCD g h b hb) ((fiberBoundaryRightBase g h b).cospanTwoTailRhs) :=
  (fiberBoundaryRhsCDWithHEq g h b hb).property

/-- 概要：左の基底データは全ての既知集合で方程式を満たす。
方針：零未知データの既知方程式の回収を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの微分整合式に必要な生の方程式。 -/
lemma fiberBoundaryLeftBase_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (I : Finset (Fin (n + 4))) (hI : ¬ cospanPrefixFaces n ⊆ I) :
    (fiberBoundaryLeftBase g h b).Equation I :=
  cospanBoundaryLeftData_equation (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) I hI

/-- 概要：左の基底データの先頭の未知成分は零。
方針：零未知データの先頭成分の零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭残差を右辺の負へ書き換える。 -/
lemma fiberBoundaryLeftBase_prefixHom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h))) :
    (fiberBoundaryLeftBase g h b).cospanPrefixHom = 0 :=
  cospanBoundaryLeftZeroData_prefixHom (A := A) (D := Complex A) (n := n) (sliceOverUncurry b)

/-- 概要：左の基底データの全ての未知成分は零。
方針：零未知データの全未知集合での零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：三角形の Bianchi の未知残差を右辺の負へ変える。 -/
lemma fiberBoundaryLeftBase_unknownHom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (fiberBoundaryLeftBase g h b).hom I a c k hI ha hc hk = 0 :=
  cospanBoundaryLeftZeroData_unknownHom (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) I hprefix a c k hI ha hc hk

/-- 概要：右の基底データは全ての既知集合で方程式を満たす。
方針：零未知データの既知方程式の回収を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの微分整合式に必要な生の方程式。 -/
lemma fiberBoundaryRightBase_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (I : Finset (Fin (n + 4))) (hI : ¬ cospanPrefixFaces n ⊆ I) :
    (fiberBoundaryRightBase g h b).Equation I :=
  cospanBoundaryRightData_equation (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) I hI

/-- 概要：右の基底データの先頭の未知成分は零。
方針：零未知データの先頭成分の零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭残差を右辺の負へ書き換える。 -/
lemma fiberBoundaryRightBase_prefixHom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h))) :
    (fiberBoundaryRightBase g h b).cospanPrefixHom = 0 :=
  cospanBoundaryRightZeroData_prefixHom (A := A) (D := Complex A) (n := n) (sliceOverUncurry b)

/-- 概要：右の基底データの全ての未知成分は零。
方針：零未知データの全未知集合での零性を使う。
規約：HA Proposition 1.3.1.10。使われ方：三角形の Bianchi の未知残差を右辺の負へ変える。 -/
lemma fiberBoundaryRightBase_unknownHom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (a c : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (fiberBoundaryRightBase g h b).hom I a c k hI ha hc hk = 0 :=
  cospanBoundaryRightZeroData_unknownHom (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) I hprefix a c k hI ha hc hk

end SerrePositivity.InfinityCategories.DGNerve

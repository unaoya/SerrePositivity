module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryResiduals
public import SerrePositivity.InfinityCategories.DGNerve.PullbackBoundaryEquations

/-! # 実際の境界の未知成分の明示候補

概要：標準 fiber の逆座標から未知の先頭成分を作り、D 側成分を右三角形の右辺とする。
方針：三座標の逆同型に既知の右辺の負を入れ、座標の等式を評価する。
規約：HTT §1.2.13、N7.1。使われ方：直接の境界充填で追加する二つの非零未知成分。
ここでは射影と三角形の代数式だけを確認し、先頭・D 側の微分方程式は後で検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：未知の先頭成分の候補は既知の三右辺の逆座標の負。
方針：実際の境界からの r_B,r_C,r_CD−r_BD を Hom-fiber の逆同型へ入れる。
規約：HTT §1.2.13、N7.1。使われ方：未知の先頭成分 a の直接の値。 -/
def fiberBoundaryUnknownA {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (pullbackFiber g h) (fiberBoundaryDegree n + 1) :=
  pullbackHomBoundaryLift g h (fiberBoundaryDegree n)
    (fiberBoundaryRhsB g h b hb) (fiberBoundaryRhsC g h b hb)
    (fiberBoundaryRhsCD g h b hb - fiberBoundaryRhsBD g h b hb)

/-- 概要：未知の D 側成分の候補は右三角形側の既知の右辺。
方針：標準 fiber の右三角形のホモトピーが零なので d=r_CD と取る。
規約：HTT §1.2.13、N7.1。使われ方：未知の D 側成分 d の直接の値。 -/
def fiberBoundaryUnknownD {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) D (fiberBoundaryDegree n) :=
  fiberBoundaryRhsCD g h b hb

/-- 概要：実際の先頭候補の B 射影は対応する右辺の負。
方針：Hom-fiber の逆座標の射影公式を実際の右辺に適用する。
規約：HTT §1.2.13、N7.1。使われ方：B 側の未知成分を零とした方程式。 -/
lemma fiberBoundaryUnknownA_projectionB {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryUnknownA g h b hb).comp (Cochain.ofHom (pullbackProjectionB g h))
      (add_zero (fiberBoundaryDegree n + 1)) = -fiberBoundaryRhsB g h b hb := by
  unfold fiberBoundaryUnknownA
  exact pullbackHomBoundaryLift_projectionB g h (fiberBoundaryDegree n) _ _ _

/-- 概要：実際の先頭候補の C 射影は対応する右辺の負。
方針：Hom-fiber の逆座標の射影公式を実際の右辺に適用する。
規約：HTT §1.2.13、N7.1。使われ方：C 側の未知成分を零とした方程式。 -/
lemma fiberBoundaryUnknownA_projectionC {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryUnknownA g h b hb).comp (Cochain.ofHom (pullbackProjectionC g h))
      (add_zero (fiberBoundaryDegree n + 1)) = -fiberBoundaryRhsC g h b hb := by
  unfold fiberBoundaryUnknownA
  exact pullbackHomBoundaryLift_projectionC g h (fiberBoundaryDegree n) _ _ _

/-- 概要：実際の先頭候補と標準ホモトピーの合成は二つの三角形側右辺の差の負。
方針：Hom-fiber の逆座標の第三成分の公式を使う。
規約：HTT §1.2.13、N7.1。使われ方：二つの三角形成分を零とした方程式の差。 -/
lemma fiberBoundaryUnknownA_homotopy {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryUnknownA g h b hb).comp
      (fiberNullHomotopy (fiberDifference g h)) (by omega) =
      -(fiberBoundaryRhsCD g h b hb - fiberBoundaryRhsBD g h b hb) := by
  unfold fiberBoundaryUnknownA
  exact pullbackHomBoundaryLift_homotopy g h (fiberBoundaryDegree n) _ _ _

/-- 概要：実際の先頭候補と対角射の合成は C 側右辺と h の合成の負。
方針：逆座標の C 射影の公式と対角射の厳密な合成表示を使う。
規約：HTT §1.2.13、N7.1。使われ方：D 側の候補の微分方程式の右辺。 -/
lemma fiberBoundaryUnknownA_diagonal {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryUnknownA g h b hb).comp (Cochain.ofHom (pullbackDiagonal g h))
      (add_zero (fiberBoundaryDegree n + 1)) =
      -(fiberBoundaryRhsC g h b hb).comp (Cochain.ofHom h)
        (add_zero (fiberBoundaryDegree n + 1)) := by
  unfold fiberBoundaryUnknownA
  exact pullbackHomBoundaryLift_diagonal g h (fiberBoundaryDegree n) _ _ _

/-- 概要：実際の候補 a,d と零の左三角形成分は左三角形の代数式を満たす。
方針：逆座標の第三成分の公式を、d=r_CD とともに用いる。
規約：HTT §1.2.13、N7.1。使われ方：未知 e=0 の方程式。 -/
lemma fiberBoundaryUnknown_left_triangle {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (0 : Cochain (fiberBoundarySource g h b) D (fiberBoundaryDegree n)) =
      -fiberBoundaryUnknownD g h b hb - (fiberBoundaryUnknownA g h b hb).comp
        (fiberNullHomotopy (fiberDifference g h)) (by omega) + fiberBoundaryRhsBD g h b hb := by
  unfold fiberBoundaryUnknownA fiberBoundaryUnknownD
  exact pullbackBoundary_left_triangle_equation g h (fiberBoundaryDegree n) _ _ _ _

end SerrePositivity.InfinityCategories.DGNerve

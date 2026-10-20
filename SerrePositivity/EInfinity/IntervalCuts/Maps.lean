module

public import SerrePositivity.EInfinity.IntervalCuts.MapComponents

/-!
# 両端点と辺からの実際の区間射

概要：Berger–Moerdijk 命題 4.1・Berger–Fresse §3.1 の境界持ち上げに使う区間射を構成する。
方針：閉じた頂点二像と両端差を境界に持つ辺像を全整数成分へ延長する。
規約：標的は任意の非有界複体、モデル構造は仮定しない。
使われ方：具体的な区間境界の射影 cofibration 性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：指定した両端点と辺を持つ実際の区間射（BM 命題 4.1、BF §3.1）。
方針：全整数成分と生成元で確認した微分条件を束ねる。
規約：頂点像は閉元、辺の微分は終点像と始点像の差。
使われ方：全射な擬同型に対する区間境界の持ち上げ。 -/
def intervalMap (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (hv : ∀ b, K.d 0 1 (v b) = 0) (he : K.d (-1) 0 e = v 1 - v 0) : interval A ⟶ K where
  f := intervalMapComponent A K v e
  comm' r s h := by
    obtain rfl : s = r + 1 := h.symm
    exact intervalMapComponent_comm A K v e hv he r

/-- 概要：構成した区間射は指定した頂点像を持つ（BF §3.1）。
方針：零次成分の線形延長を評価する。
規約：元の正規化面生成元で述べる。
使われ方：持ち上げ射が境界上で指定された射に一致すること。 -/
lemma intervalMap_vertex (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (hv : ∀ b, K.d 0 1 (v b) = 0) (he : K.d (-1) 0 e = v 1 - v 0) (b : Fin 2) :
    (intervalMap A K v e hv he).f 0 (faceVector A (vertex b)) = v b := by
  change intervalMapComponent A K v e 0 (faceVector A (vertex b)) = _
  rw [intervalMapComponent_zero, vertexInputLift_face]

/-- 概要：構成した区間射は指定した辺像を持つ（BF §3.1）。
方針：−1 次成分の線形延長を評価する。
規約：向きは零から一。
使われ方：持ち上げ射が底の区間射の辺像を持ち上げること。 -/
lemma intervalMap_edge (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (hv : ∀ b, K.d 0 1 (v b) = 0) (he : K.d (-1) 0 e = v 1 - v 0) :
    (intervalMap A K v e hv he).f (-1) (faceVector A edge) = e := by
  change intervalMapComponent A K v e (-1) (faceVector A edge) = _
  rw [intervalMapComponent_negOne, edgeInputLift_face]

/-- 概要：区間からの複体射は両頂点と一辺で決まる（BF §3.1）。
方針：零次・−1 次は生成元外延性、他の整数次数は始域の零性を使う。
規約：標的は任意の非有界複体。
使われ方：境界持ち上げ射と元の区間射を全複体射として比較する。 -/
lemma interval_hom_ext {K : Complex A} {f g : interval A ⟶ K}
    (hv : ∀ b : Fin 2, f.f 0 (faceVector A (vertex b)) = g.f 0 (faceVector A (vertex b)))
    (he : f.f (-1) (faceVector A edge) = g.f (-1) (faceVector A edge)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro r
  by_cases hr0 : r = 0
  · subst r
    apply ModuleCat.hom_ext
    exact vertexInput_linear_ext A hv
  · by_cases hr1 : r = -1
    · subst r
      apply ModuleCat.hom_ext
      exact edgeInput_linear_ext A he
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx := interval_eq_zero_of_other A r hr0 hr1 x
      simp only [hx, map_zero]

/-- 概要：単位複体からの射は零次の一の像で決まる（BM 命題 4.1）。
方針：sphere 射と閉元の既存の同値の単射性を使う。
規約：同じ基礎環の任意の標的複体。
使われ方：持ち上げた区間射が両端点上で元の射に一致すること。 -/
lemma unit_hom_ext {K : Complex A} {f g : 𝟙_ (Complex A) ⟶ K}
    (h : f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
      g.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) : f = g := by
  apply (complexSphereHomEquiv A K 0).injective
  apply Subtype.ext
  exact h

/-- 概要：端点後の構成区間射の一の像は指定した頂点像（BM 命題 4.1）。
方針：端点の生成元公式と構成した区間射の頂点評価を連結する。
規約：false を始点、true を終点とする。
使われ方：二端点境界の持ち上げの左可換性。 -/
lemma endpoint_intervalMap_apply (K : Complex A) (v : Fin 2 → K.X 0) (e : K.X (-1))
    (hv : ∀ b, K.d 0 1 (v b) = 0) (he : K.d (-1) 0 e = v 1 - v 0) (b : Bool) :
    (endpoint A b ≫ intervalMap A K v e hv he).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        v (if b then 1 else 0) := by
  change (intervalMap A K v e hv he).f 0 ((endpoint A b).f 0
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) = _
  rw [endpoint_zero_apply, one_smul, intervalMap_vertex]

end SerrePositivity.EInfinity.IntervalCuts

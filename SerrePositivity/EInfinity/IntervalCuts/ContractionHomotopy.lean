module

public import SerrePositivity.EInfinity.IntervalCuts.ContractionValues
public import SerrePositivity.EInfinity.IntervalCuts.FaceBoundaries
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# 正規化区間の収縮の具体的な鎖ホモトピー

概要：Berger–Fresse §3.1・Berger–Moerdijk 命題 4.1 の収縮の擬同型性を証明する。
方針：一頂点を辺へ、零頂点を零へ送る次数 −1 のホモトピーを線形延長する。
規約：実際の正規化区間と単位複体を使い、モデル構造は仮定しない。
使われ方：具体的な E-coalgebra 区間の contraction_quasiIso フィールド。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：収縮ホモトピーの各整数次数成分（BF §3.1）。
方針：零次から −1 次だけ、一頂点を辺へ送り零頂点を零へ送る。
規約：それ以外の成分は零。
使われ方：実際の鎖ホモトピーの全整数成分。 -/
def contractionHomotopyComponent (r s : ℤ) : (interval A).X r ⟶ (interval A).X s :=
  if hr : r = 0 then if hs : s = -1 then
    eqToHom (congrArg (fun t => (interval A).X t) hr) ≫
      vertexInputLift A ((interval A).X (-1))
        (fun b => if b = 0 then 0 else faceVector A edge) ≫
      eqToHom (congrArg (fun t => (interval A).X t) hs.symm)
  else 0 else 0

/-- 概要：収縮ホモトピーは一頂点を辺へ送り零頂点を零へ送る（BF §3.1）。
方針：零次成分の定義と頂点線形延長の評価を使う。
規約：頂点は元の正規化面生成元。
使われ方：ホモトピー等式を区間三生成元で確認する。 -/
lemma contractionHomotopyComponent_vertex (b : Fin 2) :
    contractionHomotopyComponent A 0 (-1) (faceVector A (vertex b)) =
      if b = 0 then 0 else faceVector A edge := by
  have H : contractionHomotopyComponent A 0 (-1) =
      vertexInputLift A ((interval A).X (-1))
        (fun b => if b = 0 then 0 else faceVector A edge) := by
    simp [contractionHomotopyComponent]
  rw [H]
  exact (congrArg (fun x => vertexInputLift A ((interval A).X (-1))
    (fun b => if b = 0 then 0 else faceVector A edge) x) (faceVector_vertex_eq A b)).trans
      (vertexInputLift_vertex A _ _ b)

/-- 概要：恒等射は零端点への収縮と鎖ホモトピック（BF §3.1）。
方針：零次の両頂点と −1 次の一辺で h d + d h を確認し、他の成分は零性を使う。
規約：ホモトピーの向きは恒等射から収縮・零端点への合成。
使われ方：収縮のホモトピー逆と擬同型性を構成する。 -/
def contractionHomotopy : Homotopy (𝟙 (interval A)) (contraction A ≫ endpoint A false) where
  hom := contractionHomotopyComponent A
  zero r s h := by
    by_cases hr : r = 0
    · subst r
      by_cases hs : s = -1
      · subst s
        exact False.elim (h (by decide))
      · simp [contractionHomotopyComponent, hs]
    · simp only [contractionHomotopyComponent, dite_eq_right hr]
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel r (r + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (r - 1) r from by change (r - 1) + 1 = r; omega)]
    by_cases hr : r = 0
    · subst r
      change 𝟙 ((interval A).X 0) =
        (interval A).d 0 1 ≫ contractionHomotopyComponent A 1 0 +
          contractionHomotopyComponent A 0 (-1) ≫ (interval A).d (-1) 0 +
          (contraction A ≫ endpoint A false).f 0
      have hz : contractionHomotopyComponent A 1 0 = 0 := by
        simp only [contractionHomotopyComponent, dite_eq_right (by decide : (1 : ℤ) ≠ 0)]
      rw [hz, comp_zero, zero_add]
      apply ModuleCat.hom_ext
      apply vertexInput_linear_ext A
      intro b
      change faceVector A (vertex b) =
        (interval A).d (-1) 0 (contractionHomotopyComponent A 0 (-1)
          (faceVector A (vertex b))) +
            (contraction A ≫ endpoint A false).f 0 (faceVector A (vertex b))
      rw [contractionHomotopyComponent_vertex, contraction_endpoint_vertex]
      fin_cases b
      · simp
      · simp [faceVector_edge_d_sub]
    · by_cases hr1 : r = -1
      · subst r
        change 𝟙 ((interval A).X (-1)) =
          (interval A).d (-1) 0 ≫ contractionHomotopyComponent A 0 (-1) +
            contractionHomotopyComponent A (-1) (-2) ≫ (interval A).d (-2) (-1) +
            (contraction A ≫ endpoint A false).f (-1)
        have hz : contractionHomotopyComponent A (-1) (-2) = 0 := by
          simp only [contractionHomotopyComponent, dite_eq_right (by decide : (-1 : ℤ) ≠ 0)]
        rw [hz, zero_comp, add_zero]
        apply ModuleCat.hom_ext
        apply edgeInput_linear_ext A
        change faceVector A edge =
          contractionHomotopyComponent A 0 (-1) ((interval A).d (-1) 0 (faceVector A edge)) +
            (endpoint A false).f (-1) ((contraction A).f (-1) (faceVector A edge))
        rw [faceVector_edge_d_sub, map_sub, contractionHomotopyComponent_vertex,
          contractionHomotopyComponent_vertex, contraction_eq_zero_of_ne_zero A (-1) hr,
          map_zero]
        simp
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hx := interval_eq_zero_of_other A r hr hr1 x
        simp only [hx, map_zero]

/-- 概要：区間収縮と零端点は実際の鎖ホモトピー同値（BM 命題 4.1、BF §3.1）。
方針：端点・収縮の三角形と構成した鎖ホモトピーを束ねる。
規約：底は実際の正規化 Δ¹、係数環は任意。
使われ方：具体区間収縮の擬同型性。 -/
def contractionHomotopyEquiv : HomotopyEquiv (interval A) (𝟙_ (Complex A)) where
  hom := contraction A
  inv := endpoint A false
  homotopyHomInvId := (contractionHomotopy A).symm
  homotopyInvHomId := Homotopy.ofEq (endpoint_contraction A false)

/-- 概要：正規化区間の収縮は擬同型（BM 命題 4.1、BF §3.1）。
方針：実際の鎖ホモトピー同値の順方向射に一般定理を適用する。
規約：モデル構造や始域の cofibrancy を仮定しない。
使われ方：CoalgebraInterval の contraction_quasiIso フィールド。 -/
lemma contraction_quasiIso : QuasiIso (contraction A) :=
  (contractionHomotopyEquiv A).quasiIso_hom

/-- 概要：正規化区間の両端点は擬同型（BM 命題 4.1、BF §3.1）。
方針：収縮の擬同型性と端点・収縮の恒等合成に二対三性を使う。
規約：両端点で同じ具体的な収縮を使う。
使われ方：区間の端点を trivial cofibration として使うための弱同値条件。 -/
lemma endpoint_quasiIso (b : Bool) : QuasiIso (endpoint A b) := by
  have := contraction_quasiIso A
  have : QuasiIso (endpoint A b ≫ contraction A) := by
    rw [endpoint_contraction]
    infer_instance
  exact quasiIso_of_comp_right (endpoint A b) (contraction A)

end SerrePositivity.EInfinity.IntervalCuts

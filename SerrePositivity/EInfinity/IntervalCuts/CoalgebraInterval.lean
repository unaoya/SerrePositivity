module

public import SerrePositivity.EInfinity.IntervalCuts.EndpointCoaction
public import SerrePositivity.EInfinity.IntervalCuts.ContractionCoaction
public import SerrePositivity.EInfinity.IntervalCuts.BoundaryCofibration

/-!
# 実際の正規化区間による E-coalgebra 区間

概要：Berger–Fresse §3.1・Berger–Moerdijk 命題 4.1 の具体的な余代数区間を構成する。
方針：一般 TR と区間切断の E 余代数に、実際の端点・収縮と全区間条件を付ける。
規約：任意の可換環、非有界整数複体、追加のモデル構造仮定なし。
使われ方：E2a-3 の具体区間を完全な抽象転送へ代入する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

variable (A : Type u) [CommRing A]

/-- 概要：N_*(Δ¹) の実際の E-coalgebra 区間（BF §3.1、BM 命題 4.1）。
方針：証明済みの全 arity の余作用・端点・収縮・境界持ち上げ性を束ねる。
規約：両端点は元の頂点、収縮は AW 余単位で、任意の可換基礎環。
使われ方：具体的な E 代数の転送モデル構造と functorial path object。 -/
def coalgebraInterval : Operad.CoalgebraInterval (BarrattEccles.augmentation A) where
  coalgebra := barrattEcclesCoalgebra A
  endpoint := endpoint A
  contraction := contraction A
  endpoint_contraction := endpoint_contraction A
  endpoint_coaction := endpoint_coaction A
  contraction_coaction := contraction_coaction A
  boundary_cofibration := boundary_cofibration A
  contraction_quasiIso := contraction_quasiIso A

end SerrePositivity.EInfinity.IntervalCuts

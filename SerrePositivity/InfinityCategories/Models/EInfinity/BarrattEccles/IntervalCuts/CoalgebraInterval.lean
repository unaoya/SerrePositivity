module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EndpointCoaction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ContractionCoaction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.BoundaryCofibration

/-!
模型。文献の定義との比較は後で
# 実際の正規化区間による E-coalgebra 区間

概要：Berger–Fresse §3.1・Berger–Moerdijk 命題 4.1 の具体的な余代数区間を構成する。
方針：一般 TR と区間切断の E 余代数に、実際の端点・収縮と全区間条件を付ける。
規約：任意の可換環、非有界整数複体、追加のモデル構造仮定なし。
使われ方：E2a-3 の具体区間を完全な抽象転送へ代入する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

variable (A : Type u) [CommRing A]

/-- 概要：N_*(Δ¹) の実際の E-coalgebra 区間（BF §3.1、BM 命題 4.1）。
方針：証明済みの全 arity の余作用・端点・収縮・境界持ち上げ性を束ねる。
規約：両端点は元の頂点、収縮は AW 余単位で、任意の可換基礎環。
使われ方：具体的な E 代数の転送モデル構造と functorial path object。 -/
def coalgebraInterval : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval (_root_.SerrePositivity.EInfinity.BarrattEccles.augmentation A) where
  coalgebra := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A
  endpoint := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A
  contraction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A
  endpoint_contraction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_contraction A
  endpoint_coaction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_coaction A
  contraction_coaction := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_coaction A
  boundary_cofibration := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.boundary_cofibration A
  contraction_quasiIso := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_quasiIso A

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

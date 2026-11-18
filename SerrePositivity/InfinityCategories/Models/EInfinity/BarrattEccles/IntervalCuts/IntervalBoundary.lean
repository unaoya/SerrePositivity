module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedInterval

/-!
模型。文献の定義との比較は後で
# 正規化区間の次数制限と辺の微分

概要：Berger–Fresse §2.1–2.2 の区間の正規化鎖は零・一次だけに台を持つ。
方針：高次の標準一単体の単体は退化し、一般の正規化射影がそれを消すことを使う。
規約：N_*(Δ¹) 自身について証明し、整数表示の正次数も零とする。
使われ方：切断の成分を整数複体の射へ束ねる際の零成分と境界計算。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：区間の高次の単体の正規化生成元は零（BF §2.1）。
方針：二頂点への単射ではあり得ないので、退化正規化の消滅を使う。
規約：自然数鎖次数 q が一より大きい場合。
使われ方：区間の高次の零成分を生成元で証明する。 -/
lemma interval_generator_eq_zero (q : ℕ) (hq : 1 < q) (x : Δ[1] _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] q x = 0 := by
  let θ : ⦋q⦌ ⟶ ⦋1⦌ := SSet.stdSimplex.objEquiv x
  have hθ : ¬ Mono θ := by
    intro h
    have hi := (SimplexCategory.mono_iff_injective).mp h
    have hc := Fintype.card_le_of_injective θ.toOrderHom hi
    simp only [Fintype.card_fin] at hc
    omega
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono A Δ[1] q θ hθ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex
  have hx : (Δ[1] : SSet).map θ.op _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex = x := by
    apply SSet.stdSimplex.objEquiv.injective
    change θ ≫ 𝟙 ⦋1⦌ = SSet.stdSimplex.objEquiv x
    simp only [Category.comp_id, θ]
  rwa [hx] at h

/-- 概要：区間の自然数鎖次数 q>1 は零対象（BF §2.1）。
方針：全正規化生成元で恒等射と零射を比較する。
規約：係数環の標数を制限しない。
使われ方：区間入力の不要な鎖成分を消去する。 -/
lemma intervalChains_isZero (q : ℕ) (hq : 1 < q) :
    Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X q) := by
  apply (Limits.IsZero.iff_id_eq_zero _).2
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A Δ[1] q
  intro x
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] q x = 0
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_generator_eq_zero A q hq x

/-- 概要：区間の整数表示の正次数は零対象（BF §2.1）。
方針：自然数鎖次数を負の整数へ移す延長の像にないことを使う。
規約：整数コチェイン次数。
使われ方：余演算を全整数次数で定義する正次数の分岐。 -/
lemma interval_isZero_positive (r : ℤ) (hr : 0 < r) : Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X r) := by
  apply isZero_extend_X
  intro q
  change -(q : ℤ) ≠ r
  omega

/-- 概要：区間の負次数の微分は元の正規化鎖の微分（BF §2.1）。
方針：次数延長の微分の標準公式を使う。
規約：任意の二つの自然数鎖次数について述べる。
使われ方：切断の境界計算を整数テンソルへ移す。 -/
lemma interval_d_neg (p q : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-(p : ℤ)) (-(q : ℤ)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A p).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).d p q ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A q).inv :=
  extend_d_eq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A) ComplexShape.embeddingDownNat rfl rfl

/-- 概要：整数区間の辺の微分は二端点の差（BF §2.1）。
方針：延長の微分を正規化鎖へ戻し、実際の辺の境界を使う。
規約：整数次数 −1 から零への微分。
使われ方：χ の辺での余演算の微分保存の入力側。 -/
lemma faceVector_edge_d : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A 1 - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A 0) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_edge]
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_d_neg]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain_d]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

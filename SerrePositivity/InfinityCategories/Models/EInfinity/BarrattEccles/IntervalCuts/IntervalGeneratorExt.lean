module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IntervalInputComponents
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IntervalBoundary

/-!
模型。文献の定義との比較は後で
# 実際の区間成分の二頂点・一辺による外延性

概要：Berger–Fresse §2.2.6–7 の区間入力の線形写像を二頂点・一辺だけで比較する。
方針：零単体は頂点、一単体は恒等辺または退化であることを正規化生成元へ移す。
規約：実際の Moore 複体とその整数次数表示を使う。
使われ方：全整数の双線形 Leibniz 条件を既存の成分恒等式で検査する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 概要：区間の零単体はその唯一の頂点が指定する標準頂点（BF §2.2.1）。
方針：一元の順序集合からの写像を唯一の点で比較する。
規約：頂点は零または一。
使われ方：零成分上の射の外延性。 -/
lemma zeroSimplex_eq_vertex (x : Δ[1] _⦋0⦌) :
    x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex ((SSet.stdSimplex.objEquiv x).toOrderHom 0) := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 概要：区間の単射な一単体は標準の向き付き辺（BF §2.2.1）。
方針：二元順序集合の単射単調自己写像は両端点を保つ。
規約：単射性は単体圏の mono で与える。
使われ方：標準辺以外の正規化生成元の消滅。 -/
lemma monoOneSimplex_eq_edge (x : Δ[1] _⦋1⦌) (hm : Mono (SSet.stdSimplex.objEquiv x)) :
    x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex := by
  let θ := SSet.stdSimplex.objEquiv x
  have hi : Function.Injective θ.toOrderHom := (SimplexCategory.mono_iff_injective).mp hm
  have ho : θ.toOrderHom 0 < θ.toOrderHom 1 :=
    lt_of_le_of_ne (θ.toOrderHom.monotone (by decide)) (by
      intro he
      exact (by decide : (0 : Fin 2) ≠ 1) (hi he))
  have ho' := Fin.lt_def.mp ho
  have hb0 := Fin.is_lt (θ.toOrderHom 0)
  have hb1 := Fin.is_lt (θ.toOrderHom 1)
  change (θ.toOrderHom 0).val < 2 at hb0
  change (θ.toOrderHom 1).val < 2 at hb1
  have h0 : θ.toOrderHom 0 = 0 := by
    apply Fin.ext
    change (θ.toOrderHom 0).val = 0
    omega
  have h1 : θ.toOrderHom 1 = 1 := by
    apply Fin.ext
    change (θ.toOrderHom 1).val = 1
    omega
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

variable (A : Type u) [CommRing A]

/-- 概要：標準辺以外の区間一次生成元は正規化後に零（BF §2.2.1）。
方針：単射な一単体の分類と非 mono な単体写像の正規化消滅を使う。
規約：定数の二つの退化辺をともに消す。
使われ方：一次成分の射を一辺だけで比較する。 -/
lemma interval_generator_one_eq_zero (x : Δ[1] _⦋1⦌) (hx : x ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Δ[1] 1 x = 0 := by
  let θ := SSet.stdSimplex.objEquiv x
  have hn : ¬ Mono θ := fun hm => hx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.monoOneSimplex_eq_edge x hm)
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono A Δ[1] 1 θ hn _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex
  have hxmap : (Δ[1] : SSet).map θ.op _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex = x := by
    apply SSet.stdSimplex.objEquiv.injective
    change θ ≫ 𝟙 ⦋1⦌ = SSet.stdSimplex.objEquiv x
    simp only [Category.comp_id, θ]
  rwa [hxmap] at h

/-- 概要：自然数零次の区間からの射は二頂点で決まる（BF §2.2.6）。
方針：全正規化生成元の外延性と零単体の分類を使う。
規約：終域は任意の係数加群。
使われ方：頂点入力の全線形微分条件。 -/
lemma vertexChain_hom_ext {M : ModuleCat.{u} A} {f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 0 ⟶ M}
    (h : ∀ b, f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b) = g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b)) : f = g := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A Δ[1] 0
  intro x
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroSimplex_eq_vertex x]
  exact h _

/-- 概要：自然数一次の区間からの射は標準一辺で決まる（BF §2.2.6）。
方針：標準辺以外の全生成元が零となることを使う。
規約：終域は任意の係数加群。
使われ方：辺入力の全線形微分条件。 -/
lemma edgeChain_hom_ext {M : ModuleCat.{u} A} {f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A).X 1 ⟶ M}
    (h : f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A) = g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A)) : f = g := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A Δ[1] 1
  intro x
  by_cases hx : x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSimplex
  · subst x
    exact h
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_generator_one_eq_zero A x hx, map_zero, map_zero]

/-- 概要：整数零成分からの区間射は二端点生成元で決まる（BF §2.2.6）。
方針：次数比較同型を前置して自然数零次の外延性へ戻す。
規約：実際の整数区間の射。
使われ方：全整数余演算の頂点分岐の比較。 -/
lemma vertexInput_hom_ext {M : ModuleCat.{u} A} {f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 ⟶ M}
    (h : ∀ b, f ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b)) =
      g ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b))) : f = g := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv).mp
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain_hom_ext A
  intro b
  exact h b

/-- 概要：整数一次成分からの区間射は一辺生成元で決まる（BF §2.2.6）。
方針：次数比較同型を前置して自然数一次の外延性へ戻す。
規約：整数次数 −1 の実際の区間射。
使われ方：全整数余演算の辺分岐の比較。 -/
lemma edgeInput_hom_ext {M : ModuleCat.{u} A} {f g : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-1) ⟶ M}
    (h : f ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A)) =
      g ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A))) : f = g := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv).mp
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain_hom_ext A
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

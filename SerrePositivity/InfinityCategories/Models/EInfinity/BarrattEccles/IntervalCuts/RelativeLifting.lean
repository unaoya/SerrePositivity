module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Maps
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel

/-!
模型。文献の定義との比較は後で
# 両端点を固定する正規化区間射の持ち上げ

概要：Berger–Moerdijk 命題 4.1 の区間境界の左持ち上げ性を生成元から証明する。
方針：指定両端点の差を境界とする辺を全射な擬同型に沿って持ち上げる。
規約：標的・始域の cofibrancy やモデル構造を仮定しない。
使われ方：二端点境界の射影 cofibration 性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：端点の可換三角形は生成元の像の一致を与える（BM 命題 4.1）。
方針：単位複体の零次の一で射の等式を評価する。
規約：指定された単位からの射の像は既存の sphere 閉元で読む。
使われ方：持ち上げる辺の境界の適合条件を証明する。 -/
lemma endpoint_triangle_value {K L : Complex A} (q : K ⟶ L)
    (a : 𝟙_ (Complex A) ⟶ K) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ L) (c : Bool)
    (hc : a ≫ q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A c ≫ b) :
    q.f 0 (complexSphereCycle A 0 a).val =
      b.f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (if c then 1 else 0))) := by
  have H := congrArg (fun f : 𝟙_ (Complex A) ⟶ L =>
    f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) hc
  change q.f 0 (complexSphereCycle A 0 a).val = b.f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A c).f 0
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) at H
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_zero_apply, one_smul] at H
  exact H

/-- 概要：全射な擬同型に沿い両端点を固定して区間射を持ち上げられる（BM 命題 4.1）。
方針：閉じた端点差を境界に持つ辺を持ち上げ、三生成元から複体射へ延長する。
規約：任意の非有界複体、任意の可換環。
使われ方：実際の二端点境界からの左持ち上げ性。 -/
lemma interval_relative_lift {K L : Complex A} (q : K ⟶ L)
    (hs : ∀ r : ℤ, Function.Surjective (q.f r)) (hq : QuasiIso q)
    (a₀ a₁ : 𝟙_ (Complex A) ⟶ K) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ L)
    (h₀ : a₀ ≫ q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A false ≫ b) (h₁ : a₁ ≫ q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A true ≫ b) :
    ∃ l : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ K,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A false ≫ l = a₀ ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A true ≫ l = a₁ ∧ l ≫ q = b := by
  let z₀ := complexSphereCycle A 0 a₀
  let z₁ := complexSphereCycle A 0 a₁
  let v : Fin 2 → K.X 0 := fun c => if c = 0 then z₀.val else z₁.val
  have hv₀ : v 0 = z₀.val := by simp [v]
  have hv₁ : v 1 = z₁.val := by simp [v]
  have hv (c : Fin 2) : K.d 0 1 (v c) = 0 := by
    fin_cases c
    · exact z₀.property
    · exact z₁.property
  have hq₀ : q.f 0 (v 0) = b.f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0)) := by
    rw [hv₀]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_triangle_value A q a₀ b false h₀
  have hq₁ : q.f 0 (v 1) = b.f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1)) := by
    rw [hv₁]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_triangle_value A q a₁ b true h₁
  let z : complexCycles A K 0 := ⟨v 1 - v 0, by
    change K.d 0 1 (v 1 - v 0) = 0
    rw [map_sub, hv, hv, sub_self]⟩
  have hc : q.f 0 z.val = L.d (-1) 0 (b.f (-1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) := by
    change q.f 0 (v 1 - v 0) = _
    rw [map_sub, hq₁, hq₀]
    have H := congrArg (fun f => f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) (b.comm (-1) 0)
    change L.d (-1) 0 (b.f (-1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) =
      b.f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-1) 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) at H
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_edge_d_sub, map_sub] at H
    exact H.symm
  have Hlift := complex_boundary_lifting_of_surjective_quasiIso A q hs hq (-1)
  simp only [complexBoundaryLiftAt] at Hlift
  obtain ⟨t, ht, hqt⟩ := Hlift z (b.f (-1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) hc
  let l := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap A K v t hv ht
  refine ⟨l, ?_, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_hom_ext A
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A false ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap A K v t hv ht).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_intervalMap_apply]
    exact hv₀
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.unit_hom_ext A
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A true ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap A K v t hv ht).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_intervalMap_apply]
    exact hv₁
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_hom_ext A
    · intro c
      change q.f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap A K v t hv ht).f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex c))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap_vertex]
      fin_cases c
      · exact hq₀
      · exact hq₁
    · change q.f (-1) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap A K v t hv ht).f (-1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) = _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalMap_edge]
      exact hqt

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

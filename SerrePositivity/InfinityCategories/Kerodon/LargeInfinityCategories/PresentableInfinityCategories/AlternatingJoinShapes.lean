module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplexTerminalFaceAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

/-!
概要：交互前置図式に二頂点を加える join の標準単体表示を揃える。
方針：標準単体への射の頂点検出と、join の左右の頂点の数値を使う。
規約：頂点検出は標的が標準単体の場合だけに使い、得る結論は全射の等式。
使われ方：有限交互段の再帰と全可算図式への貼り合わせ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

private lemma joinSimplexLeftVertex_val (m n : ℕ) (x : (Δ[m] : SSet.{u}) _⦋0⦌) :
    (SSet.stdSimplex.obj₀Equiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m n).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[m] Δ[n]).app _ x))).val = (SSet.stdSimplex.obj₀Equiv x).val := by
  rfl

private lemma joinSimplexRightVertex_val (m n : ℕ) (x : (Δ[n] : SSet.{u}) _⦋0⦌) :
    (SSet.stdSimplex.obj₀Equiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m n).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[m] Δ[n]).app _ x))).val = m + 1 + (SSet.stdSimplex.obj₀Equiv x).val := by
  rfl

private lemma simplexEqToHom_vertex_val {m n : ℕ} (h : m = n)
    (x : (Δ[m] : SSet.{u}) _⦋0⦌) :
    (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg
      (fun k ↦ (Δ[k] : SSet.{u})) h)).app _ x)).val = (SSet.stdSimplex.obj₀Equiv x).val := by
  cases h
  rfl

private lemma simplexMap_vertex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (Δ[m] : SSet.{u}) _⦋0⦌) :
    SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.map α).app _ x) =
      α.toOrderHom (SSet.stdSimplex.obj₀Equiv x) := rfl

private lemma stdSimplex_join_hom_ext {K L : SSet.{u}} {n : ℕ}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L ⟶ (Δ[n] : SSet.{u})}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x, y⟩
  fin_cases i
  · cases x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌)) y
  · cases y
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hl (Opposite.op ⦋0⦌)) x

/-- 概要：交互前置図式の後に二頂点を加えた形状の標準単体同型。
方針：join の標準同型と次数の算術等式を合成する。
規約：n 段から n+1 段への次数を二倍で揃える。
使われ方：次の全交互図式を元の標準単体で表示する。 -/
def alternatingSuccessorIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2 * n] : SSet.{u}) Δ[1] ≅ Δ[2 * (n + 1)] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (2 * n) 1 ≪≫
    eqToIso (congrArg (fun k ↦ (Δ[k] : SSet.{u})) (by omega : 2 * n + 1 + 1 = 2 * (n + 1)))

/-- 概要：次の偶数面は、元の偶数面と新しい辺の終点を join した全射。
方針：標準単体への全射を頂点で検出し、左右の join の頂点数値を計算する。
規約：結論は全標準単体射の厳密な等式。
使われ方：新しい表示前置図式と交互前置図式の整合。 -/
lemma sequentialEvenFace_successor_join (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n))
        (SSet.stdSimplex.δ (0 : Fin 2)) ≫ (alternatingSuccessorIso.{u} n).hom := by
  apply stdSimplex_join_hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    change (SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace (n + 1))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0]).app _ x)))).val =
      (SSet.stdSimplex.obj₀Equiv ((alternatingSuccessorIso n).hom.app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1]).app _ ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)).app _ x)))).val
    rw [simplexMap_vertex]
    change 2 * (SSet.stdSimplex.obj₀Equiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0]).app _ x))).val = _
    rw [joinSimplexLeftVertex_val n 0 x]
    change _ = (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u}))
      (by omega : 2 * n + 1 + 1 = 2 * (n + 1)))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (2 * n) 1).hom.app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1]).app _ ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)).app _ x))))).val
    rw [simplexEqToHom_vertex_val (by omega : 2 * n + 1 + 1 = 2 * (n + 1))]
    rw [joinSimplexLeftVertex_val (2 * n) 1
      ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)).app _ x)]
    rw [simplexMap_vertex]
    rfl
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    change (SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace (n + 1))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0]).app _ x)))).val =
      (SSet.stdSimplex.obj₀Equiv ((alternatingSuccessorIso n).hom.app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[2 * n] Δ[1]).app _ ((SSet.stdSimplex.δ (0 : Fin 2)).app _ x)))).val
    rw [simplexMap_vertex]
    change 2 * (SSet.stdSimplex.obj₀Equiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0]).app _ x))).val = _
    rw [joinSimplexRightVertex_val n 0 x]
    change _ = (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u}))
      (by omega : 2 * n + 1 + 1 = 2 * (n + 1)))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (2 * n) 1).hom.app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[2 * n] Δ[1]).app _ ((SSet.stdSimplex.δ (0 : Fin 2)).app _ x))))).val
    rw [simplexEqToHom_vertex_val (by omega : 2 * n + 1 + 1 = 2 * (n + 1))]
    rw [joinSimplexRightVertex_val (2 * n) 1 ((SSet.stdSimplex.δ (0 : Fin 2)).app _ x)]
    have hx : (SSet.stdSimplex.obj₀Equiv x).val = 0 := by omega
    have hy : (SSet.stdSimplex.obj₀Equiv ((SSet.stdSimplex.δ (0 : Fin 2)).app _ x)).val = 1 := by
      change (Fin.succAbove (0 : Fin 2) (SSet.stdSimplex.obj₀Equiv x)).val = 1
      simp [Fin.eq_zero (SSet.stdSimplex.obj₀Equiv x)]
    omega

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

/-!
概要：区間上の inner fibration の cocartesian fibration 性の判定。
方針：区間の辺を恒等一単体と二つの定値辺に分け、定値辺は恒等辺で持ち上げる。
規約：非退化な辺の持ち上げは零 fiber の各頂点で指定する。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、相対 join の区間への射影。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：区間の自己射は恒等射か、いずれかの端点への定値射。
方針：二頂点の像を列挙し、逆順の場合を単調性で排除する。
規約：恒等射は非退化な標準辺を表す。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、区間上の辺の持ち上げの場合分け。 -/
lemma interval_hom_eq_id_or_const (e : (Δ[1] : SSet.{u}) ⟶ Δ[1]) :
    e = 𝟙 Δ[1] ∨ ∃ i : Fin 2, e = SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  let s := SSet.yonedaEquiv e
  have hm : s 0 ≤ s 1 := (stdSimplex.objEquiv s).toOrderHom.monotone (by decide)
  generalize h0 : s 0 = i at hm
  generalize h1 : s 1 = j at hm
  fin_cases i <;> fin_cases j
  · right
    refine ⟨0, ?_⟩
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k <;> change s _ = 0 <;> assumption
  · left
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k <;> assumption
  · exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hm |>.elim
  · right
    refine ⟨1, ?_⟩
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k <;> change s _ = 1 <;> assumption

/-- 概要：区間上の inner fibration は非退化辺の cocartesian lift があれば cocartesian。
方針：標準辺を指定 lift で、定値辺を始点の恒等辺で持ち上げる。
規約：零 fiber の頂点の条件は零次成分の等式で与える。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、標準 prism から fibration 性を得る。 -/
lemma cocartesianFibration_interval_of_lift {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [Quasicategory E] [InnerFibration p]
    (h : ∀ x : E _⦋0⦌, p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ l : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ l = SSet.yonedaEquiv.symm x ∧ l ≫ p = 𝟙 Δ[1] ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv l)) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p := by
  constructor
  refine ⟨InnerFibration.mem, ?_⟩
  intro x e he
  rcases interval_hom_eq_id_or_const e with rfl | ⟨i, rfl⟩
  · apply h x
    apply SSet.yonedaEquiv.symm.injective
    rw [Category.comp_id, stdSimplex.δ_one_eq_const,
      ← SSet.yonedaEquiv_symm_zero] at he
    exact he.symm
  · have hx : p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm i := by
      apply SSet.yonedaEquiv.symm.injective
      simpa only [SSet.comp_const, SSet.yonedaEquiv_symm_zero] using he.symm
    refine ⟨SSet.const x, ?_, ?_, ?_⟩
    · rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]
    · rw [SSet.const_comp, hx]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_constant p x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

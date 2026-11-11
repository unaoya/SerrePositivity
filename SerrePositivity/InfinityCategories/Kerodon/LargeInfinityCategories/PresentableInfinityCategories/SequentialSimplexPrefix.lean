module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveStageModel
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingJoinShapes

/-!
概要：有限始区間の任意の包含を標準単体の前置面として比較する。
方針：頂点値を保つ有限順序の包含と全 nerve の標準表示を使う。
規約：すべての射を全単体上で比較する。
使われ方：二段ずつ増加する交互前置図式の全可算貼り合わせ。

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

/-- 概要：有限始区間の任意の前置包含。
方針：有限順序の頂点値を変えずに標準単体へ送る。
規約：包含の上界の証明に依存しない。
使われ方：飛ばして選んだ有限段階の厳密な遷移。 -/
def simplexPrefix {m n : ℕ} (h : m ≤ n) : (Δ[m] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.Hom.mk
    { toFun := fun i : Fin (m + 1) ↦ (⟨i.val, by omega⟩ : Fin (n + 1))
      monotone' := fun _ _ hij ↦ hij })

/-- 概要：前置包含は恒等な始区間を保持する。
方針：有限順序写像の値を展開する。
規約：全射の等式。
使われ方：段階遷移の初期条件。 -/
lemma simplexPrefix_refl (n : ℕ) : simplexPrefix.{u} (le_refl n) = 𝟙 Δ[n] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  rfl

/-- 概要：前置包含は上界の推移と厳密に整合する。
方針：有限順序写像の合成を計算する。
規約：全射の等式。
使われ方：隣接段の整合を任意の二段へ拡張する。 -/
lemma simplexPrefix_comp {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    simplexPrefix.{u} h ≫ simplexPrefix h' = simplexPrefix (h.trans h') := by
  rfl

/-- 概要：隣接する前置包含は通常の最終頂点を除く面。
方針：同じ有限順序写像として展開する。
規約：全射の等式。
使われ方：既存の逐次貼り合わせとの比較。 -/
lemma simplexPrefix_succ (n : ℕ) :
    simplexPrefix.{u} (Nat.le_succ n) = SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) := by
  rfl

/-- 概要：任意の有限始区間の包含は標準単体の前置包含に対応する。
方針：各全単体を表す有限順序写像の値を計算する。
規約：段階の差が一に限らない。
使われ方：共終な部分段階から標準単体列を貼る。 -/
lemma sequentialNerveStageSimplexIso_prefix {m n : ℕ} (h : m ≤ n) :
    Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone h) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso.{u} n).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso.{u} m).hom ≫ simplexPrefix h := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  rfl

private lemma eqToHom_vertex_value {m n : ℕ} (h : m = n)
    (x : (Δ[m] : SSet.{u}) _⦋0⦌) :
    (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg
      (fun k ↦ (Δ[k] : SSet.{u})) h)).app _ x)).val = (SSet.stdSimplex.obj₀Equiv x).val := by
  cases h
  rfl

/-- 概要：交互後続段の元の単体への包含は二段先への前置包含。
方針：標準単体への全射を頂点で検出し、標準 join 同型の順序値を計算する。
規約：結論は全射の厳密な等式。
使われ方：全交互前置図式を可算 nerve の偶数段階へ移す。 -/
lemma simplexPrefix_alternating (n : ℕ) :
    simplexPrefix.{u} (by omega : 2 * n ≤ 2 * (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  change (SSet.stdSimplex.obj₀Equiv x).val =
    (SSet.stdSimplex.obj₀Equiv ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u}))
      (by omega : 2 * n + 1 + 1 = 2 * (n + 1)))).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (2 * n) 1).hom.app _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1]).app _ x)))).val
  rw [eqToHom_vertex_value (by omega : 2 * n + 1 + 1 = 2 * (n + 1))]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

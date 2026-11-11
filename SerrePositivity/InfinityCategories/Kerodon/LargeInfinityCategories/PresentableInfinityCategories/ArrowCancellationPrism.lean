module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ArrowPushoutFamily
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-!
概要：元の合成三角形を、二本の辺と恒等射からなる射圏内の実 pushout へ送る。
方針：三時刻の単調写像を全単体の射にし、二つの評価を退化 pushout にする。
規約：元の全二単体を保持する。二対三則を仮定しない。
使われ方：実像の左消去への幾何学。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 三角形の始点側と終点側をつなぐ三時刻の単調写像。 -/
def arrowCancellationOrder : (Fin 2 × Fin 2) × Fin 2 →o Fin 3 where
  toFun z := if z.1.1 = 0 then z.1.2.castLE (by decide) else z.2.succ
  monotone' := by decide

/-- 元の合成三角形に適用する全 prism。 -/
def arrowCancellationPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[2] :=
  (α_ Δ[1] Δ[1] Δ[1]).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap arrowCancellationOrder

/-- 始点評価は、元の最初の辺を縦に恒等として伸ばす。 -/
lemma arrowCancellationPrism_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1]) ≫
    arrowCancellationPrism.{u} = fst Δ[1] Δ[1] ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  apply SSet.stdSimplex.ext
  intro i
  change (a i).castLE (by decide) = (stdSimplex.δ (2 : Fin 3)).app _ a i
  change (a i).castLE (by decide) = Fin.succAbove (2 : Fin 3) (a i)
  generalize a i = j
  fin_cases j <;> rfl

/-- 終点評価は、元の最後の辺を横に恒等として伸ばす。 -/
lemma arrowCancellationPrism_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1]) ≫
    arrowCancellationPrism.{u} = snd Δ[1] Δ[1] ≫ stdSimplex.δ (0 : Fin 3) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  apply SSet.stdSimplex.ext
  intro i
  change (b i).succ = (stdSimplex.δ (0 : Fin 3)).app _ b i
  change (b i).succ = Fin.succAbove (0 : Fin 3) (b i)
  generalize b i = j
  fin_cases j <;> rfl

/-- 左下頂点は元の最初の辺。 -/
lemma arrowCancellationPrism_vertex_first : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowCancellationPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
      stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 右下頂点は元の中間対象の恒等射。 -/
lemma arrowCancellationPrism_vertex_identity : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowCancellationPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 左上頂点は元の合成辺。 -/
lemma arrowCancellationPrism_vertex_composite : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowCancellationPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
      stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 右上頂点は元の最後の辺。 -/
lemma arrowCancellationPrism_vertex_last : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowCancellationPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) =
      stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

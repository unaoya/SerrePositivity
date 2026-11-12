module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap

/-!
概要：標準二単体を初頂点へ縮める同じ単調なホモトピー。
方針：時間零では零、時間一では元の頂点とする直積の単調写像を使う。
規約：三角形の元の三辺を保ち、辺の代表を選び直さない。
使われ方：可逆三角形の空間の評価の同値性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 三角形の初頂点から元の三角形への単調な変形。 -/
def triangleInitialContractionOrder : Fin 3 × Fin 2 →o Fin 3 where
  toFun p := if p.2 = 0 then 0 else p.1
  monotone' := by decide

/-- 元の標準二単体の初頂点から恒等写像へのホモトピー。 -/
def triangleInitialContraction :
    SSet.Homotopy (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) :
      (Δ[2] : SSet.{u}) ⟶ Δ[2]) (𝟙 _) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap triangleInitialContractionOrder
  h₀ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro i
    rfl
  h₁ := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply stdSimplex.ext
    intro i
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 初頂点での変形の辺は恒等辺そのもの。 -/
lemma triangleInitialContraction_vertex_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge triangleInitialContraction.{u}
      (stdSimplex.obj₀Equiv.symm (0 : Fin 3))).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[2] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm (0 : Fin 3))).edge := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 中間頂点での変形の辺は元の最初の辺そのもの。 -/
lemma triangleInitialContraction_vertex_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge triangleInitialContraction.{u}
      (stdSimplex.obj₀Equiv.symm (1 : Fin 3))).edge =
        SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 終頂点での変形の辺は元の長辺そのもの。 -/
lemma triangleInitialContraction_vertex_two :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge triangleInitialContraction.{u}
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3))).edge =
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

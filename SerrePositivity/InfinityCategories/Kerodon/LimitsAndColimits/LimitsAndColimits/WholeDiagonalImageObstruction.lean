module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CanonicalIntervalTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalNaturality

/-!
概要：任意の二胞体族の長辺が標準 coherent 区間比較の像に入るとは限らない。
方針：因子分解三単体を三角柱へ引き戻し、標準像が満たす終点三角形の退化条件を比較する。
規約：これは明示的な非像条件であり、(9) の強化仕様を証明済みと扱わない。
使われ方：全 T を量化する追加対角条項の仕様検査。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 三角柱の六頂点を、0,1,1,1,2,3 の順に三単体へ送る。 -/
def factorizationTrianglePrismLabel : Fin 3 × Fin 2 →o Fin 4 where
  toFun a := if a.1 = 0 then (if a.2 = 0 then 0 else 1)
    else if a.1 = 1 then 1 else if a.2 = 0 then 2 else 3
  monotone' := by decide

/-- 同じ有限座標による実三角柱写像。 -/
def factorizationTrianglePrism : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[3] where
  app _ := ↾fun s => stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom (factorizationTrianglePrismLabel.comp (prodStdSimplex.objEquiv s)))
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 三角柱の長辺の終点側三角形は、元の三単体の一番面そのもの。 -/
@[reassoc]
lemma factorizationTrianglePrism_diagonal_target_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 ≫ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
      factorizationTrianglePrism = stdSimplex.δ (1 : Fin 4) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- first 短辺の四角形は対応する指定面に厳密に含まれる。 -/
lemma factorizationTrianglePrism_first_retract :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫
      stdSimplex.σ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) =
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply stdSimplex.ext
  intro i
  change (3 : Fin 4).succAbove ((2 : Fin 3).predAbove
    (factorizationTrianglePrismLabel ((2 : Fin 3).succAbove (a i), t i))) =
    factorizationTrianglePrismLabel ((2 : Fin 3).succAbove (a i), t i)
  generalize a i = ai
  generalize t i = ti
  fin_cases ai <;> fin_cases ti <;> rfl

/-- last 短辺の四角形は対応する指定面に厳密に含まれる。 -/
lemma factorizationTrianglePrism_last_retract :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫
      stdSimplex.σ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) =
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply stdSimplex.ext
  intro i
  change (0 : Fin 4).succAbove ((0 : Fin 3).predAbove
    (factorizationTrianglePrismLabel ((0 : Fin 3).succAbove (a i), t i))) =
    factorizationTrianglePrismLabel ((0 : Fin 3).succAbove (a i), t i)
  generalize a i = ai
  generalize t i = ti
  fin_cases ai <;> fin_cases ti <;> rfl

/-- 第一短辺は厳密退化面の下で始点に定値となる座標。 -/
@[reassoc]
lemma factorizationTrianglePrism_first_projection :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫
      stdSimplex.σ (2 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply stdSimplex.ext
  intro i
  change (0 : Fin 2).predAbove ((2 : Fin 3).predAbove
    (factorizationTrianglePrismLabel ((2 : Fin 3).succAbove (a i), t i))) = 0
  generalize a i = ai
  generalize t i = ti
  fin_cases ai <;> fin_cases ti <;> rfl

/-- 第二短辺は厳密退化面の下で元の辺に定値となる座標。 -/
@[reassoc]
lemma factorizationTrianglePrism_last_projection :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫
      stdSimplex.σ (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = fst Δ[1] Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply stdSimplex.ext
  intro i
  change (1 : Fin 2).predAbove ((0 : Fin 3).predAbove
    (factorizationTrianglePrismLabel ((0 : Fin 3).succAbove (a i), t i))) = a i
  generalize a i = ai
  generalize t i = ti
  fin_cases ai <;> fin_cases ti <;> rfl

/-- 二つの指定面が通常の単位合成なら、三角柱の二短辺は元の指定定値族。 -/
lemma factorizationTrianglePrism_boundary_of_unit_faces {X : SSet.{u}}
    (F : (Δ[3] : SSet.{u}) ⟶ X) (e : (Δ[1] : SSet.{u}) ⟶ X)
    (h₀ : stdSimplex.δ (0 : Fin 4) ≫ F = stdSimplex.σ (1 : Fin 2) ≫ e)
    (h₃ : stdSimplex.δ (3 : Fin 4) ≫ F = stdSimplex.σ (0 : Fin 2) ≫ e) :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫ F =
      SSet.const (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) ∧
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ factorizationTrianglePrism ≫ F =
      fst Δ[1] Δ[1] ≫ e := by
  constructor
  · have hh := factorizationTrianglePrism_first_retract.{u} =≫ F
    simp only [Category.assoc, h₃] at hh
    rw [factorizationTrianglePrism_first_projection_assoc, SSet.const_comp] at hh
    exact hh.symm
  · have hh := factorizationTrianglePrism_last_retract.{u} =≫ F
    simp only [Category.assoc, h₀] at hh
    rw [factorizationTrianglePrism_last_projection_assoc] at hh
    exact hh.symm

/-- 終点側三角形が退化しない長辺族は、どの標準 coherent Hom 族とも厳密には一致しない。 -/
lemma factorizationTrianglePrism_diagonal_not_canonical
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Z : C)
    (F : (Δ[3] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (hF : ∀ e : (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C,
      stdSimplex.δ (1 : Fin 4) ≫ F ≠ stdSimplex.σ (1 : Fin 2) ≫ e) :
    ¬ ∃ r : (Δ[1] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z),
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max u v})) ≫
        factorizationTrianglePrism ≫ F =
        (Δ[1] ◁ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z) := by
  rintro ⟨r, hr⟩
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedIntervalFamily_target_triangle_degenerate (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Z)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫= hr
  rw [factorizationTrianglePrism_diagonal_target_triangle_assoc] at hh
  apply hF e
  refine hh.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact he

/-- 標準区間比較の像が満たす、終点側三角形の必要条件。 -/
lemma coherentIntervalFamily_target_triangle_degenerate
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Z : C)
    (r : (Δ[1] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z)) :
    ∃ e : (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (Δ[1] ◁ r) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z) =
        stdSimplex.σ (1 : Fin 2) ≫ e := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedIntervalFamily_target_triangle_degenerate (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Z)
  refine ⟨e, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact he

/-- 三単体の一番面の長辺と第一辺が異なれば、その長辺族は標準像に入らない。 -/
lemma factorizationTrianglePrism_diagonal_not_canonical_of_distinct_edges
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Z : C)
    (F : (Δ[3] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (hF : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) ≫ F ≠
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) ≫ F) :
    ¬ ∃ r : (Δ[1] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z),
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max u v})) ≫
        factorizationTrianglePrism ≫ F =
        (Δ[1] ◁ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z) := by
  apply factorizationTrianglePrism_diagonal_not_canonical X Z F
  intro e he
  apply hF
  have h₁ : (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{max u v}) ⟶ Δ[2]) ≫
      stdSimplex.σ (1 : Fin 2) = 𝟙 _ := by
    apply SSet.yonedaEquiv.injective
    decide
  have h₂ : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{max u v}) ⟶ Δ[2]) ≫
      stdSimplex.σ (1 : Fin 2) = 𝟙 _ := by
    apply SSet.yonedaEquiv.injective
    decide
  simp only [he, ← Category.assoc, h₁, h₂, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeApexEvaluationVertex

/-!
概要：指定右Kan輸送の全錐の辺は、その頂点で元の同じ定値辺になる。
方針：輸送のfixedVertexを標準1単体で評価し、定値単体の後合成則を使う。
規約：HTT 4.3.2.15（双対）、Kerodon §7.3（Tag 02Y1）の既存輸送の計算法則。
使われ方：S8 の同じ指定余単位を保つ大域比較と値比較の成分を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 同じ指定輸送の辺の頂点成分は、元の標準錐の頂点での定値辺である。 -/
lemma RightKanConeTransport.apex_edge_eq_constant
    {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    (t.edge.map ((truncation 2).map (coneApexEvaluation (rightKanShape δ c) D))).edge =
      PinchedHom.constant (rightKanCanonicalCone δ F c).vertex 1 := by
  let w : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋1⦌ :=
    ⟨PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1,
      SSet.yonedaEquiv (𝟙 Δ[1])⟩
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app t.fixedVertex (Opposite.op ⦋1⦌)) w
  change t.family.app (Opposite.op ⦋1⦌)
    ((joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1),
        SSet.yonedaEquiv (𝟙 Δ[1])) =
    (rightKanCanonicalCone δ F c).val.app (Opposite.op ⦋1⦌)
      ((joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
  rw [pinchedConstant_map, pinchedConstant_map] at hh
  rw [← coneApexEvaluation_vertex (rightKanCanonicalCone δ F c)]
  rw [coneApexEvaluation,
    SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

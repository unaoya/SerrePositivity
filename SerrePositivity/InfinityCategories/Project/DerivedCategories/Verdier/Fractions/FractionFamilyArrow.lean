module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.PointSourceCosliceData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.MarkedSpanFamilies

/-! # 元の固定第一終点 span 全体の、同じ分数評価による可変終点の矢印族 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W)

/-- 分数評価の始点は、元の span の第一終点の像そのもの。 -/
theorem fractionSpanEvaluation_source_map :
    fractionSpanEvaluation F W hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      markedSpanSource X W ≫ F := by
  have h := fractionSpanEvaluation_source F W hF
  exact h

/-- 分数評価の終点は、元の span の第二終点の像そのもの。 -/
theorem fractionSpanEvaluation_target_map :
    fractionSpanEvaluation F W hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      markedSpanTarget X W ≫ F := by
  have h := fractionSpanEvaluation_target F W hF
  exact h

/-- 第一終点を固定した元の全 span 族に、同じ分数評価を制限する。 -/
def fractionFamilyArrow (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ fractionSpanEvaluation F W hF

/-- 同じ全矢印族の始点は、固定した第一終点の像に厳密に定値。 -/
theorem fractionFamilyArrow_zero (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow F W hF x) =
      SSet.const (F.app (Opposite.op ⦋0⦌) x) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanEvaluation_source_map, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]

/-- 同じ全矢印族の終点は、元の可変第二終点の像そのもの。 -/
theorem fractionFamilyArrow_one (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow F W hF x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanEvaluation_target_map]
  rfl

/-- 元の全分数矢印族の両端を保った fat join 表示。 -/
def fractionFamilyFatDiagram (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u})
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) ⟶ Q :=
  pointSourceFatDiagram (F.app (Opposite.op ⦋0⦌) x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow F W hF x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow_zero F W hF x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyArrow_one F W hF x)

/-- 元の全族の coslice 比較は、任意に追加した補完データを仮定せずに構成できる。 -/
theorem fractionFamilyCosliceData_nonempty (x : X _⦋0⦌) :
    Nonempty (PointSourceCosliceData (F.app (Opposite.op ⦋0⦌) x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyFatDiagram F W hF x)) :=
  exists_pointSourceCosliceData _ _ _ (pointSourceFatDiagram_inl _ _ _ _ _)
    (pointSourceFatDiagram_inr _ _ _ _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

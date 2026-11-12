module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationVertex

/-!
概要：指定頂点への等式を保持して、元の錐の標準変換と円柱を表示する。
方針：頂点の等式で標準変換を輸送する。
規約：元の錐・図式・指定頂点を選び直さない。
使われ方：指定変換から実現した錐の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 元の錐の標準変換を、指定された頂点への等式だけで輸送する。 -/
def coneTransformationPointAt (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) _⦋0⦌ :=
  hv ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationVertex c

/-- 指定頂点へ輸送しても、標準変換の全円柱は同じ元の錐の円柱。 -/
lemma coneTransformationPointAt_prism (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism
      (SSet.yonedaEquiv.symm (coneTransformationPointAt c z hv)) =
        fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneCylinderMap K ≫ c.val := by
  subst z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationVertex_prism c

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionFamilyArrow
public import SerrePositivity.KST.Fibration.PointSourceCosliceFiber
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber

/-! # 元の固定第一終点 span 族から、商の同じ coslice への実評価 -/

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
  (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x : X _⦋0⦌)

/-- 同じ全族の fat join 比較データを、証明済みの存在から選ぶ。 -/
def fractionFamilyCosliceData :
    PointSourceCosliceData (F.app (Opposite.op ⦋0⦌) x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyFatDiagram F W hF x) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceData_nonempty F W hF x)

/-- 元の全 span 族から、固定した第一終点の商像の coslice への実関手。 -/
def fractionFamilyCosliceEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toCoslice

/-- 元の同じ可変第二終点の商像を、全単体で厳密に被覆する。 -/
theorem fractionFamilyCosliceEvaluation_projection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toCoslice_projection

omit [Quasicategory Q] in
/-- 両端固定の元の span 全体は、同じ可変終点射影に対して厳密に定値。 -/
theorem fixedMarkedSpanToFamily_target (y : X _⦋0⦌) :
    fixedMarkedSpanToFamily X W x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) =
      SSet.const (F.app (Opposite.op ⦋0⦌) y) := by
  change fixedMarkedSpanToFamily X W x y ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanTarget X W ≫ F) = _
  rw [← Category.assoc, fixedMarkedSpanToFamily_inclusion, ← Category.assoc,
    fixedMarkedSpan_target, SSet.const_comp]

/-- 同じ全 coslice 評価を、元の固定第二終点上の実 fiber に制限する。 -/
def fixedFractionCosliceEvaluation (y : X _⦋0⦌) : fixedMarkedSpans X W x y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
      (F.app (Opposite.op ⦋0⦌) y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toFiber (fixedMarkedSpanToFamily X W x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedMarkedSpanToFamily_target F W x y)

/-- fiber 包含との合成は、元の同じ全族の coslice 関手への制限そのもの。 -/
theorem fixedFractionCosliceEvaluation_inclusion (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (F.app (Opposite.op ⦋0⦌) y) =
      fixedMarkedSpanToFamily X W x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation, PointSourceCosliceData.toFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

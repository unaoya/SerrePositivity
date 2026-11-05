module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionFamilyArrow
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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x : X _⦋0⦌)

/-- 同じ全族の fat join 比較データを、証明済みの存在から選ぶ。 -/
def fractionFamilyCosliceData :
    PointSourceCosliceData (F.app (Opposite.op ⦋0⦌) x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyFatDiagram F W hF x) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData_nonempty F W hF x)

/-- 元の全 span 族から、固定した第一終点の商像の coslice への実関手。 -/
def fractionFamilyCosliceEvaluation :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily X W x ⟶ sliceUnder (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toCoslice

/-- 元の同じ可変第二終点の商像を、全単体で厳密に被覆する。 -/
theorem fractionFamilyCosliceEvaluation_projection :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x ≫
      sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)) =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toCoslice_projection

omit [Quasicategory Q] in
/-- 両端固定の元の span 全体は、同じ可変終点射影に対して厳密に定値。 -/
theorem fixedMarkedSpanToFamily_target (y : X _⦋0⦌) :
    fixedMarkedSpanToFamily X W x y ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection X W x ≫ F) =
      SSet.const (F.app (Opposite.op ⦋0⦌) y) := by
  change fixedMarkedSpanToFamily X W x y ≫
    (vertexFiberι (markedSpanSource X W) x ≫ markedSpanTarget X W ≫ F) = _
  rw [← Category.assoc, fixedMarkedSpanToFamily_inclusion, ← Category.assoc,
    fixedMarkedSpan_target, SSet.const_comp]

/-- 同じ全 coslice 評価を、元の固定第二終点上の実 fiber に制限する。 -/
def fixedFractionCosliceEvaluation (y : X _⦋0⦌) : fixedMarkedSpans X W x y ⟶
    vertexFiber (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
      (F.app (Opposite.op ⦋0⦌) y) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toFiber (fixedMarkedSpanToFamily X W x y)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedMarkedSpanToFamily_target F W x y)

/-- fiber 包含との合成は、元の同じ全族の coslice 関手への制限そのもの。 -/
theorem fixedFractionCosliceEvaluation_inclusion (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y ≫
      vertexFiberι (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (F.app (Opposite.op ⦋0⦌) y) =
      fixedMarkedSpanToFamily X W x y ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation, PointSourceCosliceData.toFiber, vertexFiberLift_ι]
  rfl

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceEvaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceEvaluation_inclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedMarkedSpanToFamily_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedMarkedSpanToFamily_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionFamilyCosliceData := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionFamilyCosliceEvaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionFamilyCosliceEvaluation_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceEvaluation_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceEvaluation.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation.eq_1

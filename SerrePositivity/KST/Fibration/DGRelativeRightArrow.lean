module
public import SerrePositivity.KST.Fibration.DGInputArrowData
public import SerrePositivity.KST.Fibration.DGNuKZeroCofinality
public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity

/-! # 相対 Verdier 四角形の同じ右辺と、その ν 像の元の商射を照合する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 元の相対四角形の右辺そのものから回収する、同じ dg 入力射のデータ。 -/
def dgRelativeRightArrowData := dgInputArrowData A (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow d.square).edge

/-- 同じ右辺の ν 像は、指定した像の Verdier 提示の元の商辺に厳密に一致する。 -/
theorem dgRelativeRightArrow_nu_edge :
    (dgKInputNu A).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow d.square).edge =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.image.projection).edge := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.square ≫ dgKInputNu A)).edge := rfl
    _ = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow d.image.square).edge :=
      congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow s).edge) d.image_eq
    _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.image.square) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge _
    _ = _ := (congrArg SSet.yonedaEquiv d.image.right_edge).trans
      (SSet.yonedaEquiv.apply_symm_apply _)

/-- 復元した同じ dg 右射の ν 作用は、元の商の普遍性から本質的全射。 -/
theorem dgRelativeRightArrow_nu_essentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (dgKInputNuMap A (dgRelativeRightArrowData A d).2.2).hom :=
  dgInputArrowData_nu_essentiallySurjective A _ d.image.projection
    (dgRelativeRightArrow_nu_edge A d)
    (localization_isEssentiallySurjective d.image.projection.hom _ d.image.isVerdier.quotient)

/-- 相対四角形の同じ dg 右射の三角圏 K₀ 作用は全射。 -/
theorem dgRelativeRightArrow_kZero_surjective :
    Function.Surjective (dgNuKZeroMap A (dgRelativeRightArrowData A d).2.2) :=
  stableKZeroMap_surjective_of_essentiallySurjective _
    (dgRelativeRightArrow_nu_essentiallySurjective A d)

end SerrePositivity.KST.Fibration

module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPieceKanIndex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalDiagram

/-!
概要：指定 fiber は、部分添字射影の同じ左 Kan 局所添字に right cofinal に入る。
方針：通常の comma への fiber 包含の各右 comma に、元の値を始対象として構成する。
規約：比較は元の全空間への射影を厳密に保持する。
使われ方：coherent な左 Kan 延長の値を、元の小さい部分余極限として読む。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 指定 fiber を、部分添字射影の元の左 comma へ含める関手。 -/
def smallPieceFiberToComma (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    A.val ⥤ CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece A where
  obj x := CostructuredArrow.mk (Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalFiber A).obj x) (𝟙 A)
  map f := CostructuredArrow.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalFiber A).map f) (by subsingleton)

/-- fiber 包含の各右 comma は、元の値そのものを始対象として持つ。 -/
lemma smallPieceFiberToComma_initial (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I)
    (b : CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece A) :
    ∃ c : StructuredArrow b (smallPieceFiberToComma A), Nonempty (IsInitial c) := by
  let x : A.val := ⟨b.left.val.2, (leOfHom b.hom) b.left.property⟩
  let f : b ⟶ (smallPieceFiberToComma A).obj x :=
    CostructuredArrow.homMk (homOfLE ⟨leOfHom b.hom, le_refl _⟩) (by subsingleton)
  refine ⟨StructuredArrow.mk f, ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · exact StructuredArrow.homMk (homOfLE (leOfHom y.hom.left).2)
      (by apply CostructuredArrow.hom_ext; subsingleton)
  · intro y g
    apply StructuredArrow.hom_ext
    subsingleton

/-- 元の fiber 包含の同じ nerve 写像は right cofinal。 -/
lemma smallPieceFiberToComma_isRightCofinal (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (smallPieceFiberToComma A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma _ (smallPieceFiberToComma_initial A)

/-- 元の fiber から元の native な左 Kan 局所添字への比較。 -/
def smallPieceFiberKanComparison (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    nerve A.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A) :=
  nerveMap (smallPieceFiberToComma A) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece A).hom

/-- 同じ native な局所比較は right cofinal。 -/
lemma smallPieceFiberKanComparison_isRightCofinal (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (smallPieceFiberKanComparison A) :=
  (smallPieceFiberToComma_isRightCofinal A).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece A).hom)

/-- 同じ局所比較は、全空間の元の fiber 包含を厳密に回収する。 -/
lemma smallPieceFiberKanComparison_projection (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    smallPieceFiberKanComparison A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection
      (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A) =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalFiber A) := by
  dsimp only [smallPieceFiberKanComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

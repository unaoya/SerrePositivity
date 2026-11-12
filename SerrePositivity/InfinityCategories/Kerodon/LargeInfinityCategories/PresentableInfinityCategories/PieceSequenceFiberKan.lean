module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPieceFiberCofinal

/-!
概要：増大部分 poset 列の指定段は、段射影の左 Kan 局所添字へ共終に入る。
方針：各右 comma に元の実対象を始対象として入れる。
規約：全空間への指定 fiber 包含を厳密に保持。使われ方：列の Kan 延長値の部分余極限判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 元の指定段の fiber を、段射影の元の左 comma に含める。 -/
def pieceSequenceFiberToComma (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    (A n).val ⥤ CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A) (ULift.up n) where
  obj x := CostructuredArrow.mk (Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n).obj x) (𝟙 (ULift.up n))
  map f := CostructuredArrow.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n).map f) (by subsingleton)

/-- 増大性により各 comma の元の値は指定段に入り、その右 comma の始対象となる。 -/
lemma pieceSequenceFiberToComma_initial
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) (n : ℕ)
    (b : CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A) (ULift.up n)) :
    ∃ c : StructuredArrow b (pieceSequenceFiberToComma A n), Nonempty (IsInitial c) := by
  have hbn : b.left.val.1 ≤ (ULift.up n : ULift.{u} ℕ) := leOfHom b.hom
  let x : (A n).val := ⟨b.left.val.2, hA hbn b.left.property⟩
  let f : b ⟶ (pieceSequenceFiberToComma A n).obj x :=
    CostructuredArrow.homMk (homOfLE ⟨hbn, le_refl _⟩) (by subsingleton)
  refine ⟨StructuredArrow.mk f, ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · exact StructuredArrow.homMk (homOfLE (leOfHom y.hom.left).2)
      (by apply CostructuredArrow.hom_ext; subsingleton)
  · intro y g
    apply StructuredArrow.hom_ext
    subsingleton

/-- 指定段から左 comma への元の nerve 写像は right cofinal。 -/
lemma pieceSequenceFiberToComma_isRightCofinal
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (pieceSequenceFiberToComma A n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma _ (pieceSequenceFiberToComma_initial A hA n)

/-- 指定段から native な元の左 Kan 局所添字への比較。 -/
def pieceSequenceFiberKanComparison
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    nerve (A n).val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n)) :=
  nerveMap (pieceSequenceFiberToComma A n) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A) (ULift.up n)).hom

/-- 元の同じ局所比較は native に right cofinal。 -/
lemma pieceSequenceFiberKanComparison_isRightCofinal
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (pieceSequenceFiberKanComparison A n) :=
  (pieceSequenceFiberToComma_isRightCofinal A hA n).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A) (ULift.up n)).hom)

/-- この局所比較から、元の指定 fiber の全包含を厳密に回収する。 -/
lemma pieceSequenceFiberKanComparison_projection
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    pieceSequenceFiberKanComparison A n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n)) =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n) := by
  dsimp only [pieceSequenceFiberKanComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceFiberKan

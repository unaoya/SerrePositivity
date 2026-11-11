module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPieceKanIndex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit

/-!
概要：元の全空間上の図式を、部分添字への射影に沿って coherent に左 Kan 延長する。
方針：小さい κ-filtered 局所添字の余極限を宇宙同型で移し、F1B の存在定理を適用する。
規約：元の図式と全単位変換を保持。延長の値を個別に選ぶだけでは済ませない。
使われ方：濃度変更の部分余極限の coherent な族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]
  {C : SSet.{u + 1}} [Quasicategory C]

/-- 各点の元の局所 Kan 図式は、小さい κ-filtered 余極限の存在だけで余極限を持つ。 -/
lemma smallPiece_leftKanDiagram_hasColimit (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotal κ μ I)) ⟶ C)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece)) F v) := by
  rcases v with ⟨v⟩
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective v
  let p := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece (κ := κ) (μ := μ) (I := I))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallPiece_leftKanShape_isKappaFiltered A
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)
  have he : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map p) F
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)) ≫ F := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection]
  have hsmall : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (e.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map p) F (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A))) := by
    rw [he]
    exact hC (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)) _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasColimit_of_equivalentRestriction e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence _ hsmall

/-- 部分添字への元の射影に沿う、一つの全単位変換を持つ coherent な左 Kan 拡張の存在。 -/
lemma smallPiece_exists_leftKanExtension (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotal κ μ I)) ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I)) ⟶ C)
      (β : SSet.Homotopy F
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece) ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece)) F G β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits _ F (smallPiece_leftKanDiagram_hasColimit hC F)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

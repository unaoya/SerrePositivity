module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRightKanLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.HomotopyComponentTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.RightKanTransportComponents

/-!
# 元の実右 Kan 単位の全成分の可逆性

概要：任意の実右 Kan 単位の同じ全実成分が可逆と証明する。
方針：元の二つの極限錐の脚から frame 上で回収し、次数零の augmentation で戻す。
規約：元の単位も全ホモトピーも成分も選び直さない。
使われ方：全反転関手への本質的全射性と ∞ 局所化普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma cofibrantSourceFrameRightKanMap_frame_projection (X : CofibrantAlgebra A)
    (n : AsSmall.{u + 1} SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (cofibrantHammockVertex A X)).app (Opposite.op ⦋0⦌)
      ((cofibrantSourceFrameRightKanMap A X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((cofibrantDKSourceFrame A X).obj n) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (cofibrantSourceFrameRightKanMap_projection A X) (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)
  rw [NatTrans.comp_app_apply] at h
  exact h.trans (ComposableArrows.ext₀ rfl)

lemma cofibrantSourceRightKanUnit_frame_isInvertible (X : CofibrantAlgebra A)
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A) ⟶ E)
    (α : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      F G α) (n : AsSmall.{u + 1} SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((cofibrantDKSourceFrame A X).obj n))).toTruncated := by
  obtain ⟨t, ht⟩ := hα (cofibrantHammockVertex A X)
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n
  let v := (cofibrantSourceFrameRightKanMap A X).app (Opposite.op ⦋0⦌) i
  have hqG := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_inverts (cofibrantAlgebraRelativeCategory A)).comp G
  have h₀ := cofibrantSourceRightKanLimitCone_leg_isInvertible A X _ hqG
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      G (cofibrantHammockVertex A X))
    (cofibrantSourceRightKanCanonicalCone_isLimit A X G) i
  have h₁ := cofibrantSourceRightKanLimitCone_leg_isInvertible A X F hF t.cone ht i
  have hi := t.component_isInvertible_of_legs v h₀ h₁
  exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α z).toTruncated)
      (cofibrantSourceFrameRightKanMap_frame_projection A X n)).mp hi

lemma cofibrantSourceRightKanUnit_vertex_isInvertible (X : CofibrantAlgebra A)
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A) ⟶ E)
    (α : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      F G α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from X))).toTruncated := by
  let n : AsSmall.{u + 1} SimplexCategory := ⟨⦋0⦌⟩
  let e := (nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).toTruncated
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyComponent_target_isInvertible α e
    (cofibrantSourceRightKanUnit_frame_isInvertible A X F hF G α hα n)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G)))
      (f := ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G)).toTruncated)
      rfl).mpr (cofibrantSourceFrameAugmentation_image_invertible A X _
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_inverts (cofibrantAlgebraRelativeCategory A)).comp G) n)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map F))
      (f := ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map F).toTruncated)
      rfl).mpr (cofibrantSourceFrameAugmentation_image_invertible A X F hF n)

lemma cofibrantSourceRightKanUnit_isInvertible
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (G : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A) ⟶ E)
    (α : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      F G α) (z : (nerve (cofibrantAlgebraRelativeCategory A).category) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α z).toTruncated := by
  let X : CofibrantAlgebra A := z.obj 0
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from X) = z :=
    ComposableArrows.ext₀ rfl
  exact (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α t).toTruncated)
    hz).mp (cofibrantSourceRightKanUnit_vertex_isInvertible A X F hF G α hα)

end SerrePositivity.EInfinity.BarrattEccles

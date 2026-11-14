module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape
public import SerrePositivity.EInfinity.FrameHom.FrameAugmentationLimitLegs
public import SerrePositivity.EInfinity.FrameHom.FrameRightKanCanonical
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.HomotopyComponentTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeLegRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.RightKanTransportComponents
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCanonicalMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightPrecompositionFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RightKanCriterion

/-!
概要：同じ bifibrant frame の余終性を三つの実 right Kan 判定入力に還元する。
方針：代数版の元の極限・標準錐・指定単位の証明を一般モデル圏へ移す。
規約：余終性は未証明の明示入力として残し、局所化普遍性の完成と扱わない。
使われ方：一般モデルの frame→hammock 比較から局所化普遍性への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (q : ∀ X : BifibrantObject C, CofibrantResolution (C := C) simplex X.obj)
  (hcofinal : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantFrameRightKanMap X (q X)))


include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
def modelBifibrantHammockObject
    (z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌) : BifibrantObject C :=
  AsSmall.down.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
    (C := KanHammockCategory (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) z)

/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantHammockVertex_object
    (z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌) :
    modelBifibrantHammockVertex (modelBifibrantHammockObject z) = z :=
  (hammockLocalizationNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (modelBifibrantHammockObject z))).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
        (C := KanHammockCategory (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) z)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanDiagram_hasLimit (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      F (modelBifibrantHammockVertex X)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal (modelBifibrantFrameRightKanMap X (q X))
    (hcofinal X)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (modelBifibrantFrameRightKanMap_diagram X (q X) F)).mpr
    (modelBifibrantFrame_hasLimit X (q X) F hF)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      F z) :=
  (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) F t))
      (modelBifibrantHammockVertex_object z)).mp
    (modelBifibrantSourceRightKanDiagram_hasLimit q hcofinal (modelBifibrantHammockObject z) F hF)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantInvertingFunctor_rightKanExtension_exists
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) :
    ∃ (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E)
      (α : SSet.Homotopy
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G) F),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
          F G α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_of_local_limits
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) F
    (modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality q hcofinal F hF)



include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanCanonicalCone_isLimit (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G
      (modelBifibrantHammockVertex X)) :=
  FrameHom.FrameArrows.frameRightKanCanonicalCone_isLimit (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X (q X))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X))
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (modelBifibrantFrameAugmentation_invertible X (q X))
    (hcofinal X) modelFrameIndex_weaklyContractible G

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanCanonicalCone_isLimit_all
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E)
    (z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G z) :=
  (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G t))
      (modelBifibrantHammockVertex_object z)).mp
    (modelBifibrantSourceRightKanCanonicalCone_isLimit q hcofinal (modelBifibrantHammockObject z) G)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanExtension_refl_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G) G
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanExtension_refl_of_canonicalLimits
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G
    (modelBifibrantSourceRightKanCanonicalCone_isLimit_all q hcofinal G)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantHammockLocalizationPrecomposition_isFullyFaithful
    (E : SSet.{max u v}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) E) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.localizationPrecomposition_isFullyFaithful_of_rightKan _ _ _
    (fun _ _ => modelBifibrantSourceRightKanExtension_refl_of_frameCofinality q hcofinal) E


section Legs
variable (X : BifibrantObject C)

include q in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceFrameAugmentation_image_invertible
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (n : AsSmall.{max u v} SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated := by
  have hw := hF (show ComposableArrows.mk₁ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n) ∈
      weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) from
    ⟨_, _, _, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation_weak X (q X) n, rfl⟩)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n))).map
      ((truncation 2).map F)) at hw
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n))).map
      ((truncation 2).map F))
    (f := ((nerve.edgeMk ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated)
    rfl).mp hw

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanLimitCone_leg_isInvertible
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) F
      (modelBifibrantHammockVertex X))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (i : (nerve (AsSmall.{max u v} SimplexCategory)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c
      ((modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) i)) := by
  let u := modelBifibrantFrameRightKanMap X (q X)
  have hu := hcofinal X
  have he := modelBifibrantFrameRightKanMap_diagram X (q X) F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X (q X)) ≫ F) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).val, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u).property.trans he⟩
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLimitCone_congr he (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u) d rfl).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal u hu _ c).mp hc)
  have h := FrameHom.FrameArrows.augmentationLimitCone_leg_isInvertible
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X (q X)) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)) F
    (modelBifibrantSourceFrameAugmentation_image_invertible q X F hF)
    modelFrameIndex_weaklyContractible d hd i
  have he' : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d i).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeConeLeg_restrict_edge c u i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he').mp h

end Legs


include q in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceFrameRightKanMap_frame_projection (X : BifibrantObject C)
    (n : AsSmall.{max u v} SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X)).app (Opposite.op ⦋0⦌)
      ((modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X (q X)).obj n) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (modelBifibrantFrameRightKanMap_projection X (q X)) (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)
  rw [NatTrans.comp_app_apply] at h
  exact h.trans (ComposableArrows.ext₀ rfl)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_frame_isInvertible (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      F G α) (n : AsSmall.{max u v} SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X (q X)).obj n))).toTruncated := by
  obtain ⟨t, ht⟩ := hα (modelBifibrantHammockVertex X)
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n
  let v := (modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) i
  have hqG := (hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).comp G
  have h₀ := modelBifibrantSourceRightKanLimitCone_leg_isInvertible q hcofinal X _ hqG
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      G (modelBifibrantHammockVertex X))
    (modelBifibrantSourceRightKanCanonicalCone_isLimit q hcofinal X G) i
  have h₁ := modelBifibrantSourceRightKanLimitCone_leg_isInvertible q hcofinal X F hF t.cone ht i
  have hi := t.component_isInvertible_of_legs v h₀ h₁
  exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α z).toTruncated)
      (modelBifibrantSourceFrameRightKanMap_frame_projection q X n)).mp hi

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_vertex_isInvertible (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      F G α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X))).toTruncated := by
  let n : AsSmall.{max u v} SimplexCategory := ⟨⦋0⦌⟩
  let e := (nerve.edgeMk ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n)).toTruncated
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyComponent_target_isInvertible α e
    (modelBifibrantSourceRightKanUnit_frame_isInvertible q hcofinal X F hF G α hα n)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G)))
      (f := ((nerve.edgeMk ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n)).map
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G)).toTruncated)
      rfl).mpr (modelBifibrantSourceFrameAugmentation_image_invertible q X _
        ((hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).comp G) n)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e.map ((truncation 2).map F))
      (f := ((nerve.edgeMk ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated)
      rfl).mpr (modelBifibrantSourceFrameAugmentation_image_invertible q X F hF n)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_isInvertible_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      F G α) (z : (nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α z).toTruncated := by
  let X : BifibrantObject C := AsSmall.down.obj (z.obj 0)
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) = z :=
    ComposableArrows.ext₀ rfl
  exact (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α t).toTruncated)
    hz).mp (modelBifibrantSourceRightKanUnit_vertex_isInvertible q hcofinal X F hF G α hα)


include q hcofinal in
/-- 概要：同じ frame の余終性から bifibrant hammock の局所化普遍性を得る。
方針：三つの実 right Kan 入力を既存の判定に代入する。
規約：余終性は明示入力で残る。使われ方：その証明後の一般モデル局所化。
-/
lemma modelBifibrantHammock_isLocalization_of_frameCofinality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_rightKan_local_limits
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
  · intro E _ G
    exact modelBifibrantSourceRightKanExtension_refl_of_frameCofinality q hcofinal G
  · intro E _ F hF z
    exact modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality q hcofinal F hF z
  · intro E _ F hF G α hα x
    exact modelBifibrantSourceRightKanUnit_isInvertible_of_frameCofinality q hcofinal F hF G α hα x

end SerrePositivity.EInfinity.SimplicialLocalization

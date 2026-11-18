module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeRepresentative
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportComparisonVertex

/-!
概要：元のweightedSectionsの指定大域比較の成分を、同じ余単位の輸送錐の比較で表す。
方針：元の全関手比較・hom_facと、証明した代表移送の実際のKan条件を使う。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の既存構成の自然性の法則。
  元の全関手、指定余単位の類、weightedSections_valueTransportの選択を保つ。
使われ方：S8 の元の指定値比較と大域比較の成分との照合。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の全関手比較の成分は、同じ指定余単位の類に沿う任意の輸送錐との比較に一致する。 -/
lemma weightedSections_nativeShape_comparison_transport_vertex (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
    (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
    (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    let b := ((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
    ∀ s : RightKanConeTransport (oppositeSpaceYoneda C) O G (functorHomHomotopy b) P,
    let t := weightedSections_valueTransport O hE P
    let ht := weightedSections_valueTransport_isLimit O hE P
    let hs := (isRightKanExtension_iff_forall_transport _ _ _ _).mp
      (weightedSections_nativeShape_counit_isRightKan O hE β hβ) P s
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E)) t.cone_vertex.symm) ≫
      (limitVertexIso t.cone s.cone ht hs).hom ≫
        eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E)) s.cone_vertex) =
      functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P := by
  dsimp only
  intro s
  exact rightKanTransport_comparison_vertex (weightedSectionsData O hE).2.val
    (functorHomHomotopy _) (weightedSections_nativeShape_comparison O hE β hβ)
    (by simpa only [functorHomHomotopy_hom] using
      weightedSections_nativeShape_comparison_hom_fac O hE β hβ)
    P (weightedSections_valueTransport O hE P) s
    (weightedSections_valueTransport_isLimit O hE P)
    ((isRightKanExtension_iff_forall_transport _ _ _ _).mp
      (weightedSections_nativeShape_counit_isRightKan O hE β hβ) P s)

end SerrePositivity.InfinityCategories.Sheaves

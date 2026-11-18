module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomRepresentativeTransfer

/-!
概要：実Yoneda模型の指定余単位の同じ類を、元の固定Yoneda射に沿う実際の右Kan延長へ戻す。
方針：既存の大域比較のhom_facと、同じ類のホモトピー代表への係数移送を使う。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の既存構成の法則。
  Hom普遍性から点ごとのKan条件を仮定せず、元のweightedSectionsのKan条件から証明する。
使われ方：S8 の同じ指定大域比較と、元の指定錐の頂点比較の接続。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ元の大域比較を保ち、添字同型で移した余単位の代表に実際の右Kan条件を与える。 -/
lemma weightedSections_nativeShape_counit_isRightKan (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
    (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
    (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β) :
    let b := ((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
    IsRightKanExtension (oppositeSpaceYoneda C) O G (functorHomHomotopy b) := by
  dsimp only
  exact isRightKanExtension_homRepresentative_of_compatible_functorIso
    (weightedSectionsData O hE).2.val _
    (weightedSections_nativeShape_comparison O hE β hβ)
    (weightedSections_nativeShape_comparison_hom_fac O hE β hβ)
    (weightedSections_isRightKanExtension O hE)

end SerrePositivity.InfinityCategories.Sheaves

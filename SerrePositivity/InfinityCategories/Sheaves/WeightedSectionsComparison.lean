module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsData
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal

/-!
概要：同じ指定変換を持つ重み付き切断の模型を、元の全関手と大域的に比較する。
方針：既存の右 Kan の大域的一意性と指定変換への分解則をそのまま使う。
規約：点ごとの同型を集める構成は行わず、全関手の一つの同型を返す。
使われ方：HTT 5.1.5.6、Kerodon §7.3（Tag 02Y1）、S8 の自然な模型比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
  (O : Presheaf C E)
  (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
  {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
  (β : SSet.Homotopy (oppositeSpaceYoneda C ≫ G) O)
  (hβ : IsRightKanExtension (oppositeSpaceYoneda C) O G β)

/-- 元の同じ切断関手と指定した別の右 Kan 模型の大域的比較。
HTT 5.1.5.6、Kerodon §7.3（Tag 02Y1）、既存の指定右 Kan 比較の特殊化。 -/
def weightedSections_comparison : FunctorIso (weightedSections O hE) G :=
  kanRightKanExtensionIso (oppositeSpaceYoneda C) (weightedSectionsData O hE).2.val β
    (weightedSections_isRightKanExtension O hE) hβ

/-- 同じ大域的比較は、元の指定右 Kan 変換に両立する。
HTT 5.1.5.6、Kerodon §7.3（Tag 02Y1）、既存の分解則。 -/
lemma weightedSections_comparison_hom_fac :
    rightKanHomMap (oppositeSpaceYoneda C)
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
      (weightedSections O hE) (weightedSections_comparison O hE β hβ).hom =
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weightedSectionsData O hE).2.val) :=
  kanRightKanExtensionIso_hom_fac (oppositeSpaceYoneda C)
    (weightedSectionsData O hE).2.val β (weightedSections_isRightKanExtension O hE) hβ

/-- 指定変換に両立する全関手間の射は、同じ比較同型の射に一意。
HTT 5.1.5.6、Kerodon §7.3（Tag 02Y1）、既存の射の一意性。 -/
lemma weightedSections_comparison_hom_unique (η : FunctorHom (weightedSections O hE) G)
    (hη : rightKanHomMap (oppositeSpaceYoneda C)
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
        (weightedSections O hE) η =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (weightedSectionsData O hE).2.val)) :
    η = (weightedSections_comparison O hE β hβ).hom :=
  kanRightKanExtensionIso_hom_unique (oppositeSpaceYoneda C)
    (weightedSectionsData O hE).2.val β (weightedSections_isRightKanExtension O hE) hβ η hη

end SerrePositivity.InfinityCategories.Sheaves

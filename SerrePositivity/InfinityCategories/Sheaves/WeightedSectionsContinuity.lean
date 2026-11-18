module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.NativeShapeSectionsContinuity
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsData
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanIndexIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：元の全重み付き切断関手は、任意の小さい余極限を極限へ送る。
方針：HTT 5.1.5.6 の双対の実 Yoneda 模型を、既存の大域的 Hom 普遍性の比較で戻す。
規約：Hom 普遍性は指定 Kan 延長から証明し、点ごとの同型を組み立てない。
使われ方：切断の押し出し・局所同値の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
  (O : Presheaf C E)
  (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
  {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
  (α : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
  (hα : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G α)

/-- 指定形状の実 Yoneda 模型と元の全切断関手の大域的比較。
HTT 5.1.5.6 の双対。両方の Hom 普遍性を既存の指定 Kan 延長から証明する。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site と presentable 係数の指定反対 Yoneda 模型の比較に特殊化する。"]
def weightedSections_nativeShape_comparison : FunctorIso (weightedSections O hE) G :=
  rightKanHomUniversalIso (oppositeSpaceYoneda C)
    (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weightedSectionsData O hE).2.val))
    (((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (kanRightKanExtension_homUniversal _ _ (weightedSections_isRightKanExtension O hE))
    (RightKanHomUniversal.indexIso (fixedOppositeSetYoneda_nativeIso C)
      (kanRightKanExtension_homUniversal _ α hα))

/-- 同じ大域比較は、添字同型で移した元の指定余単位の類に両立する。
HTT 5.1.5.6 の双対の指定変換の法則。 -/
lemma weightedSections_nativeShape_comparison_hom_fac :
    rightKanHomMap (oppositeSpaceYoneda C)
      (((fixedOppositeSetYoneda_nativeIso C).postcomp G).hom ≫
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
      (weightedSections O hE) (weightedSections_nativeShape_comparison O hE α hα).hom =
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weightedSectionsData O hE).2.val) :=
  rightKanHomUniversalIso_hom_fac _ _ _
    (kanRightKanExtension_homUniversal _ _ (weightedSections_isRightKanExtension O hE))
    (RightKanHomUniversal.indexIso (fixedOppositeSetYoneda_nativeIso C)
      (kanRightKanExtension_homUniversal _ α hα))

/-- 元の全切断関手は、元の任意小余極限錐の全反転を極限錐へ送る。
HTT 5.1.5.6 の双対。形状と全余錐は drafts の元の型のまま。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site と presentable 係数の重み付き切断による全小余極限の反転（双対）。"]
theorem sectionsOf_colimit {I : SSet.{u}}
    {p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafCat C SpaceInfinity.{u}}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsLimitCone (mapJoinCone (weightedSections O hE) (coconeReverseCone c)) := by
  obtain ⟨H, ε, hε, hH⟩ := exists_nativeShapeSections_continuous O hE
  let e := weightedSections_nativeShape_comparison O hE ε hε
  exact (hH c hc).of_functorIso
    (FunctorIso.precomp (f := H) (g := weightedSections O hE)
      e.symm (coconeReverseCone c).val)

end SerrePositivity.InfinityCategories.Sheaves

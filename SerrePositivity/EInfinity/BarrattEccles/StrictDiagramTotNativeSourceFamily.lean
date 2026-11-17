module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotNativeConeAt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceApex

/-!
概要：元の同じBE Totのnative錐について、極限判定の始域Homの全族と頂点での等式を明示する。
方針：既存のCAlg頂点の全単射で同じ頂点を指定し、既存の錐全体の標準族へ代入する。
規約：IS-W2 R03の既存判定の特殊化。制限写像の同値性を仮定で代用して完成とは数えない。
使われ方：元の同じnative錐のa・ha・heを別々に照合する入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotNativeSourceFamilyModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotNativeSourceFamilyFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeSourceFamilyCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y
attribute [local instance] cAlg_sHom_kanComplex

/-- 元の錐の同じ頂点を、既存のCAlg頂点の全単射で読む。 -/
def strictBETotNativeConeSourceObject
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) : CAlgSimplicialCategory A :=
  (cAlgVertexEquiv A).symm (strictBETotNativeConeAt A F).vertex

/-- 選択した頂点表示は元の同じnative錐の頂点に厳密に等しい。 -/
theorem strictBETotNativeConeSourceObject_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex =
      coherentNerveVertex (strictBETotNativeConeSourceObject A F) :=
  ((cAlgVertexEquiv A).apply_symm_apply (strictBETotNativeConeAt A F).vertex).symm

/-- 元の同じnative錐全体上の、始域Hom全体の標準族a。 -/
def strictBETotNativeConeSourceFamily
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    (SSet.uliftFunctor.{u+1,u+1}).obj
      (SimplicialCategory.sHom X (strictBETotNativeConeSourceObject A F)).op ⟶
        coherentConeSectionSpace (strictBETotNativeConeAt A F).val (coherentNerveVertex X) :=
  coherentConeSourceFamily (strictBETotNativeConeAt A F) (strictBETotNativeConeSourceObject A F)
    (strictBETotNativeConeSourceObject_vertex A F) X

/-- 同じ族aの頂点での評価は、標準のcoslice fiber比較そのもの（ha）。 -/
theorem strictBETotNativeConeSourceFamily_evaluation
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    strictBETotNativeConeSourceFamily A F X ≫
      coherentConeApexEvaluation (strictBETotNativeConeAt A F) (strictBETotNativeConeSourceObject A F)
        (strictBETotNativeConeSourceObject_vertex A F) X =
      coherentCosliceFiberComparison X (strictBETotNativeConeSourceObject A F) :=
  coherentConeSourceFamily_evaluation _ _ _ _

/-- 同じ族aの制限が同値なら、元の同じnative錐が極限（heをこれから示す判定）。 -/
theorem strictBETotNativeConeAt_isLimit_of_sourceRestriction
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (he : ∀ X : CAlgSimplicialCategory A,
      IsSimplicialHomotopyEquivalence (strictBETotNativeConeSourceFamily A F X ≫
        coneSectionRestriction (strictBETotNativeConeAt A F) (coherentNerveVertex X))) :
    IsLimitCone (strictBETotNativeConeAt A F) :=
  coherentCone_isLimit_of_family_lifts _ _ (strictBETotNativeConeSourceObject_vertex A F)
    (strictBETotNativeConeSourceFamily A F) (strictBETotNativeConeSourceFamily_evaluation A F) he

end SerrePositivity.EInfinity.BarrattEccles

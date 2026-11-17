module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotNativeConeAt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceApex

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の同じBE Totのnative錐について、極限判定の始域Homの全族と頂点での等式を明示する。
方針：既存のCAlg頂点の全単射で同じ頂点を指定し、既存の錐全体の標準族へ代入する。
規約：IS-W2 R03の既存判定の特殊化。制限写像の同値性を仮定で代用して完成とは数えない。
使われ方：元の同じnative錐のa・ha・heを別々に照合する入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotNativeSourceFamilyModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotNativeSourceFamilyFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeSourceFamilyCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.cAlg_sHom_kanComplex

/-- 元の錐の同じ頂点を、既存のCAlg頂点の全単射で読む。 -/
def strictBETotNativeConeSourceObject
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) : _root_.SerrePositivity.EInfinity.BarrattEccles.CAlgSimplicialCategory A :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgVertexEquiv A).symm (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).vertex

/-- 選択した頂点表示は元の同じnative錐の頂点に厳密に等しい。 -/
theorem strictBETotNativeConeSourceObject_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).vertex =
      coherentNerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject A F) :=
  ((_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgVertexEquiv A).apply_symm_apply (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).vertex).symm

/-- 元の同じnative錐全体上の、始域Hom全体の標準族a。 -/
def strictBETotNativeConeSourceFamily
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (X : _root_.SerrePositivity.EInfinity.BarrattEccles.CAlgSimplicialCategory A) :
    (SSet.uliftFunctor.{u+1,u+1}).obj
      (SimplicialCategory.sHom X (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject A F)).op ⟶
        coherentConeSectionSpace (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).val (coherentNerveVertex X) :=
  coherentConeSourceFamily (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject A F)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject_vertex A F) X

/-- 同じ族aの頂点での評価は、標準のcoslice fiber比較そのもの（ha）。 -/
theorem strictBETotNativeConeSourceFamily_evaluation
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (X : _root_.SerrePositivity.EInfinity.BarrattEccles.CAlgSimplicialCategory A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceFamily A F X ≫
      coherentConeApexEvaluation (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject A F)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject_vertex A F) X =
      coherentCosliceFiberComparison X (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject A F) :=
  coherentConeSourceFamily_evaluation _ _ _ _

/-- 同じ族aの制限が同値なら、元の同じnative錐が極限（heをこれから示す判定）。 -/
theorem strictBETotNativeConeAt_isLimit_of_sourceRestriction
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (he : ∀ X : _root_.SerrePositivity.EInfinity.BarrattEccles.CAlgSimplicialCategory A,
      IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceFamily A F X ≫
        coneSectionRestriction (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F) (coherentNerveVertex X))) :
    IsLimitCone (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F) :=
  coherentCone_isLimit_of_family_lifts _ _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceObject_vertex A F)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceFamily A F) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeSourceFamily_evaluation A F) he

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-!
概要：指定BK実現の標準余単体対象のHomは、同じframe HomのBK endと自然同型。
方針：既存の随伴Hom同型と標準単体のYoneda同型を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の実際の写像空間の比較。
規約：指定した随伴を保持し、モデル構造や弱同値性をこの同定の仮定としない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C)

/-- 同じ随伴の転置とYonedaから得る、標的に自然なHom同型。 -/
def bousfieldKanRealizationHomIso :
    cosimplicialHom (SSet.stdSimplex ⋙ bousfieldKanParameterRealization K A) ≅
      hom K A ⋙ weightedSectionsFunctor (bousfieldKanWeight Kᵒᵖ) :=
  adjunctionHomIsoSameUniverse (bousfieldKanParameterAdjunction K A) SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft _ QuillenStandardFrame.homIso ≪≫ Functor.rightUnitor _

/-- 全次数の値は、指定随伴による転置のYoneda評価そのもの。 -/
lemma bousfieldKanRealizationHomIso_hom_app (Y : C) (n : SimplexCategoryᵒᵖ)
    (f : (bousfieldKanParameterRealization K A).obj (SSet.stdSimplex.obj n.unop) ⟶ Y) :
    (((bousfieldKanRealizationHomIso K A).hom.app Y).app n) f =
      SSet.yonedaEquiv ((bousfieldKanParameterAdjunction K A).homEquiv _ Y f) := rfl

end SerrePositivity.DiagramModel.FrameWeightRealization

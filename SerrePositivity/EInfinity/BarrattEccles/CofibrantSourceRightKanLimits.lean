module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameRightKanCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence

/-!
# 元の Kan hammock の実右 Kan 局所極限

概要：任意の擬同型反転関手について全頂点の実右 Kan 局所極限を得る。
方針：元の source frame 次数比較に沿って既存の極限を移送する。
規約：任意可換環・任意 quasicategory 標的・元の全頂点を保持する。
使われ方：全反転関手の右 Kan 拡張による組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

def cofibrantHammockObject
    (z : (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌) : CofibrantAlgebra A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := KanHammockCategory (cofibrantAlgebraRelativeCategory A)) z

lemma cofibrantHammockVertex_object
    (z : (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌) :
    cofibrantHammockVertex A (cofibrantHammockObject A z) = z :=
  (hammockLocalizationNerveMap_vertex (cofibrantAlgebraRelativeCategory A)
    (show (cofibrantAlgebraRelativeCategory A).category from cofibrantHammockObject A z)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
        (C := KanHammockCategory (cofibrantAlgebraRelativeCategory A)) z)

lemma cofibrantSourceRightKanDiagram_hasLimit (X : CofibrantAlgebra A)
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      F (cofibrantHammockVertex A X)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal (cofibrantSourceFrameRightKanMap A X)
    (cofibrantSourceFrameRightKanMap_isLeftCofinal A X)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (cofibrantSourceFrameRightKanMap_diagram A X F)).mpr
    (cofibrantSourceFrame_hasLimit A X F hF)

lemma cofibrantSourceRightKanDiagram_hasLimit_all
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A)))
    (z : (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      F z) :=
  (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram
    (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) F t))
      (cofibrantHammockVertex_object A z)).mp
    (cofibrantSourceRightKanDiagram_hasLimit A (cofibrantHammockObject A z) F hF)

lemma cofibrantInvertingFunctor_rightKanExtension_exists
    {E : SSet.{u + 1}} [Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A))) :
    ∃ (G : kanHammockNerve (cofibrantAlgebraRelativeCategory A) ⟶ E)
      (α : SSet.Homotopy
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) ≫ G) F),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
          F G α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_of_local_limits
    (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) F
    (cofibrantSourceRightKanDiagram_hasLimit_all A F hF)

end SerrePositivity.EInfinity.BarrattEccles

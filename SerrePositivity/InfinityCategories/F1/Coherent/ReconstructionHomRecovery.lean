module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTestFamilyFullyFaithful
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldTestFamilyComparison

/-!
概要：標準 Hom の族の共同比較から、実際の復元自己関手の全空間側の同型を回収する。
方針：Hom の族への後合成の充満忠実性で、既存の全パラメーターの同型を戻す。
規約：対象ごとの逆射を選び直さず、一つの関手同型を構成する。
使われ方：weighted nerve と元の left fibration の自然な復元比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 元の復元自己関手の反変表示は、全空間上の恒等関手と一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionOppositeIso (C : Type u) [Category.{u} C] :
    FunctorIso (𝟙 (SimplicialNerve (LeftFibrationObject (nerve C))ᵒᵖ))
      (coherentNerveMap (simplicialEnrichedOpposite (strictTransportWeightedEnriched C))) := by
  apply (leftFibrationHomTestFamily_isFullyFaithful (nerve C)).preimageFunctorIso
  simpa only [Category.id_comp] using leftStrictTransportReconstructionHomFamilyIso C

/-- 同じ復元同型を全空間の恒等射へ結ぶ、反変表示上の実際の単体的ホモトピー。 -/
def leftStrictTransportReconstructionOppositeHomotopy (C : Type u) [Category.{u} C] :
    SSet.Homotopy (𝟙 (SimplicialNerve (LeftFibrationObject (nerve C))ᵒᵖ))
      (coherentNerveMap (simplicialEnrichedOpposite (strictTransportWeightedEnriched C))) :=
  (leftStrictTransportReconstructionOppositeIso C).simplicialHomotopy

end SerrePositivity.InfinityCategories

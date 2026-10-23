module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightWeightedClassification
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransport

/-!
概要：共同 weighted 分類の全図式と比較同型を、元の Indκ の中へ戻す。
方針：元の strict 分類像の所属を同じ大域同型で輸送し、充満忠実な包含で同型を回収。
規約：包含後は元の全比較そのもの。使われ方：大域密度の右制限を比較する標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v))

include hF in
/-- 同じ共同 weighted 分類の全頂点は Indκ に属する。 -/
lemma strictRightWeightedClassification_isIndVertex (v) :
    IsIndVertex κ C ((strictRightWeightedClassification F).app (Opposite.op ⦋0⦌) v) :=
  isIndVertex_isoClosed κ C ((strictRightWeightedClassificationIso F).app v).symm (hF v)

/-- 元の共同 weighted 分類の全図式を Indκ 内へ持ち上げる。 -/
def weightedIndClassification :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ IndInfinity κ C :=
  fullSubcomplexLift (IsIndVertex κ C) (strictRightWeightedClassification F)
    (strictRightWeightedClassification_isIndVertex κ F hF)

lemma weightedIndClassification_inclusion :
    weightedIndClassification κ F hF ≫ indInclusionPresheaf κ C =
      strictRightWeightedClassification F := fullSubcomplexLift_ι _ _ _

/-- 同じ全添字上の比較は Indκ 内でも一つの関手同型を与える。 -/
def weightedIndClassificationIso :
    FunctorIso (weightedIndClassification κ F hF)
      (fullSubcomplexLift (IsIndVertex κ C)
        (HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C) hF) :=
  (indInclusionPresheaf_isFullyFaithful κ C).preimageFunctorIso
    (F2.functorIsoOfEq (strictRightWeightedClassificationIso F)
      (weightedIndClassification_inclusion κ F hF).symm (fullSubcomplexLift_ι _ _ _).symm)

/-- 包含に戻した比較は、端点輸送を除いて元の全図式の指定比較そのもの。 -/
lemma weightedIndClassificationIso_inclusion :
    HEq ((weightedIndClassificationIso κ F hF).postcomp (indInclusionPresheaf κ C))
      (strictRightWeightedClassificationIso F) := by
  unfold weightedIndClassificationIso
  exact (heq_of_eq (IsFullyFaithful.preimageFunctorIso_postcomp
    (indInclusionPresheaf_isFullyFaithful κ C) _)).trans (F2.functorIsoOfEq_heq _ _ _)

end SerrePositivity.InfinityCategories.F2.Ind

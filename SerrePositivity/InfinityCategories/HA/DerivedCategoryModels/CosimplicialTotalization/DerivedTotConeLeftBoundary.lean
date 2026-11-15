module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotClosedVertexEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotFamilyBoundaries

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ全Tot頂点族を元の通常導来入口で読む。 -/
theorem nativeTotApexFamily_derived :
    nativeTotApexFamily A ≫ complexSemifreeResolutionInfinity A =
      fst (nerve (CosimplicialObject (Complex A))) (Δ[0] : SSet.{u+1}) ≫
        derivedTotVertexFamily A := by
  unfold nativeTotApexFamily
  erw [nativeTotClosedVertexEvaluation_full A (productTotalFunctor A ⋙ complexToClosed A)]
  rfl

/-- D02の左境界：標準零単体からの射影で同じ全Tot関手へ戻る。 -/
theorem derivedTotConeFamily_left :
    (joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
      snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A))) ≫
        derivedTotVertexFamily A := by
  have he :
      (joinInl (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
        𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ (β_ _ _).hom ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv) =
      (β_ (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A)))).hom ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinInl (Δ[0] : SSet.{u+1})
            ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality,
      Category.assoc, id_tensorHom, ← whiskerLeft_comp, joinInl_joinMap, Category.id_comp]
  have h := congrArg (fun k => k ≫ nativeTotJoinFamily A ≫
    complexSemifreeResolutionInfinity A) he
  simp only [Category.assoc] at h
  have ht := congrArg (fun k =>
      (β_ (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A)))).hom ≫
        k ≫ complexSemifreeResolutionInfinity A) (nativeTotJoinFamily_apex A)
  simp only [Category.assoc] at ht
  have h' := h.trans ht
  rw [nativeTotApexFamily_derived] at h'
  have hb := braiding_hom_fst (Δ[0] : SSet.{u+1})
    (nerve (CosimplicialObject (Complex A)))
  have hb' := congrArg (fun k => k ≫ derivedTotVertexFamily A) hb
  simp only [Category.assoc] at hb'
  have h'' := h'.trans hb'
  exact h''

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

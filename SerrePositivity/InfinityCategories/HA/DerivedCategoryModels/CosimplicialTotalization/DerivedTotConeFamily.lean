module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinEvaluation
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
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- D01：同じ指定全Tot錐の全図式射・全高次単体の族。 -/
def derivedTotConeFamily :
    join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
        nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A :=
  (β_ _ _).hom ≫
    (nerve (CosimplicialObject (Complex A)) ◁
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv) ≫
        nativeTotJoinFamily A ≫ _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A

/-- 同じ全族の固定パラメータ制限は、元の同じ全strict Tot錐。 -/
theorem derivedTotConeFamily_at_lift (X : CosimplicialObject (Complex A)) :
    lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
      (SSet.const (ComposableArrows.mk₀ X)) ≫ derivedTotConeFamily A =
        (strictDerivedTotCone X).val := by
  have he :
      lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
          (SSet.const (ComposableArrows.mk₀ X)) ≫ (β_ _ _).hom ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv) =
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv ≫
        lift (SSet.const (ComposableArrows.mk₀ X)) (𝟙 _) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  have h := congrArg (fun k => k ≫ nativeTotJoinFamily A ≫
    _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A) he
  simp only [Category.assoc] at h
  have ht := congrArg (fun k =>
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv ≫ k ≫
      _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A) (nativeTotJoinFamily_at A X)
  simp only [Category.assoc] at ht
  rw [strictDerivedTotCone, joinConeOfDiagramEq_val]
  exact h.trans ht

/-- D03：標準零単体で指定した同じ点への制限は、元の全strict錐。 -/
theorem derivedTotConeFamily_at (X : CosimplicialObject (Complex A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        derivedTotConeFamily A = (strictDerivedTotCone X).val := by
  have hs :
      inv (fst (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
          (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) =
      lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
          (SSet.const (ComposableArrows.mk₀ X)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id,
        IsIso.inv_hom_id, lift_fst]
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro τ
      rfl
  rw [← Category.assoc, hs]
  exact derivedTotConeFamily_at_lift A X

/-- D04：頂点族の図式射の像は、同じ積Tot関手の像そのもの。 -/
theorem derivedTotConeFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge :=
  derivedTotVertexFamily_map A f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

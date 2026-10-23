module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStandardTargetFactorization
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramAnodyneRestriction

/-!
概要：恒等二単体の元の target 制限は、同じ元の射として自明 Kan fibration。
方針：標準内ホーンの inner anodyne 性と同じ pullback 表示の同型で移送する。
規約：元の分類図式の同じ二辺制限を保持し、同値性を追加仮定にしない。
使われ方：二単体上の同じ元の分類 Hom 作用の同値性の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 恒等二単体の同じ標準内ホーンの表示は inner anodyne。 -/
lemma cocartesianTwoSimplexStandardHorn_id_innerAnodyne :
    innerAnodyneExtensions
      (cocartesianTwoSimplexStandardHorn (𝟭 (ULift.{u} (Fin 3)))) := by
  have hi : nerveMap (𝟭 (ULift.{u} (Fin 3))) = 𝟙 _ := rfl
  dsimp only [cocartesianTwoSimplexStandardHorn]
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]
  exact innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (innerAnodyneExtensions.of_isIso _)

variable (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))

/-- 同じ標準内ホーン上の target Segal 射は、全パラメーターで自明 Kan。 -/
lemma cocartesianTwoSimplexStandardHornTargetSegalMap_id_trivialKanFibration :
    TrivialKanFibration
      (cocartesianTwoSimplexStandardHornTargetSegalMap (𝟭 _) p q) := by
  have h := intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne
    (cocartesianTwoSimplexStandardHorn (𝟭 (ULift.{u} (Fin 3))))
    cocartesianTwoSimplexStandardHorn_id_innerAnodyne
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (trivialKanFibrations.of_isIso _)⟩

/-- 恒等二単体の元の target 制限自身は、同じ元の二辺への自明 Kan 制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_id_trivialKanFibration :
    TrivialKanFibration (cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q) := by
  have : IsIso (cocartesianTwoSimplexStandardTargetPullbackMap (𝟭 _) p q) :=
    cocartesianTwoSimplexStandardTargetPullbackMap_isIso _ p q
  have hf : cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q =
      cocartesianTwoSimplexStandardHornTargetSegalMap (𝟭 _) p q ≫
        inv (cocartesianTwoSimplexStandardTargetPullbackMap (𝟭 _) p q) := by
    rw [← cocartesianTwoSimplexTargetRestrictionMap_standard_factor, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [hf]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (cocartesianTwoSimplexStandardHornTargetSegalMap_id_trivialKanFibration p q).mem
    (trivialKanFibrations.of_isIso _)⟩

/-- 同じ元の target 制限は、追加仮定なしに quasicategory の同値。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_id_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoSimplexTargetRestrictionMap (𝟭 _) p q) := by
  have := cocartesianTwoSimplexTargetRestrictionMap_id_trivialKanFibration p q
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories

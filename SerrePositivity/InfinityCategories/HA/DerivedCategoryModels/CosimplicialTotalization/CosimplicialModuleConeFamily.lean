module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence

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
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- curryの既存評価則を標準零単体の同じ固定パラメータで読む。 -/
theorem moduleConeCurry_evaluateAt {K D : SSet.{u+1}}
    (H : nerve (CosimplicialObject (ModuleCat.{u} A)) ⊗ K ⟶ D)
    (M : CosimplicialObject (ModuleCat.{u} A)) :
    curry H ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      lift (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) (𝟙 K) ≫ H := by
  let v : 𝟙_ SSet.{u+1} ⟶ nerve (CosimplicialObject (ModuleCat.{u} A)) :=
    (SSet.unitHomEquiv _).symm (ComposableArrows.mk₀ M)
  have h := curry_evaluateFunctorAt_unitHomEquiv H v
  have hv : SSet.unitHomEquiv _ v = ComposableArrows.mk₀ M :=
    (SSet.unitHomEquiv _).apply_symm_apply _
  rw [hv] at h
  have hg : (λ_ K).inv ≫ (v ▷ K) =
      lift (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) (𝟙 K) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [← Category.assoc, hg] at h
  exact h

/-- D07：交代余面頂点を固定した同じ全離散錐族。 -/
def cosimplicialModuleConeFamily :
    join (Δ[0] : SSet.{u+1}) ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A :=
  (β_ _ _).hom ≫ uncurry (discreteCochainFunctorCone A).val

/-- 同じ全離散評価の通常導来像。 -/
def discreteTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A :=
  (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) ≫ derivedTotEvaluationFamily A

/-- 同じ全離散錐族の点制限を全join射で読む。 -/
theorem cosimplicialModuleConeFamily_at_lift (M : CosimplicialObject (ModuleCat.{u} A)) :
    lift (𝟙 _) (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) ≫ cosimplicialModuleConeFamily A =
      (cosimplicialModuleCone A M).val := by
  have h := moduleConeCurry_evaluateAt A
    (uncurry (discreteCochainFunctorCone A).val) M
  rw [curry_uncurry] at h
  have hs : lift (𝟙 (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
      (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) ≫ (β_ _ _).hom =
    lift (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) (𝟙 _) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [cosimplicialModuleConeFamily, ← Category.assoc, hs,
    cosimplicialModuleCone, joinConeOfDiagramEq_val]
  exact h.symm

/-- D07の点制限は標準零単体の指定点による制限でも同じ全錐。 -/
theorem cosimplicialModuleConeFamily_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) ≫ cosimplicialModuleConeFamily A =
        (cosimplicialModuleCone A M).val := by
  have hs : inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) =
    lift (𝟙 _) (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id,
        IsIso.inv_hom_id, lift_fst]
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro τ
      rfl
  rw [← Category.assoc, hs]
  exact cosimplicialModuleConeFamily_at_lift A M

/-- 全離散錐族の両境界は同じ交代余面全関手と同じ元の全評価。 -/
theorem cosimplicialModuleConeFamily_boundaries :
    (joinInl (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A =
        snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (ModuleCat.{u} A))) ≫
          nerveMap (discreteCochainFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A ∧
    (joinInr (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A = discreteTotEvaluationFamily A := by
  constructor
  · have hv := congrArg SSet.yonedaEquiv.symm (discreteCochainFunctorCone_vertex A)
    rw [JoinCone.vertex_eq, Equiv.symm_apply_apply] at hv
    have hh := discreteTotFunctorVertex_curry_fst
      (nerveMap (discreteCochainFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
    have hhv := congrArg SSet.yonedaEquiv.symm hh
    rw [Equiv.symm_apply_apply] at hhv
    rw [← hhv] at hv
    rw [cosimplicialModuleConeFamily, ← Category.assoc,
      BraidedCategory.braiding_naturality, Category.assoc, id_tensorHom,
      ← uncurry_natural_left, hv, uncurry_curry, ← Category.assoc,
      braiding_hom_fst]
  · rw [cosimplicialModuleConeFamily, ← Category.assoc,
      BraidedCategory.braiding_naturality, Category.assoc, id_tensorHom,
      ← uncurry_natural_left, (discreteCochainFunctorCone A).property,
      rawDiscreteTotFunctorDiagram, uncurry_curry, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
    rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotFunctorCosliceFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone

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
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- cosliceの既存curry/uncurryの逆則：固定左因子と全セルでjoin射を照合する。 -/
theorem nativeTotJoin_cell_ext {K L T : SSet.{u+1}} {f g : join K L ⟶ T}
    (hleft : joinInl K L ≫ f = joinInl K L ≫ g)
    (hc : ∀ (n : ℕ) (σ : L _⦋n⦌),
      joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ f =
        joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ g) : f = g := by
  have h : sliceUnderCurry f rfl = sliceUnderCurry g hleft.symm := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact hc n σ
  have he := congrArg sliceUnderUncurry h
  rw [sliceUnderUncurry_curry, sliceUnderUncurry_curry] at he
  exact he

/-- 固定した図式での全join族の各セルは、元の同じdg錐の各セル。 -/
theorem nativeTotJoinFamily_at_cell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
      (lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
        nativeTotJoinFamily A) =
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
        (nativeDGCone X).val := by
  have he :
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
        lift (SSet.const (ComposableArrows.mk₀ X)) (𝟙 _) =
      lift (SSet.const (ComposableArrows.mk₀ X)) (𝟙 _) ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [← Category.assoc, he, Category.assoc, nativeTotJoinFamily_cell,
    nativeTotWeightedCellFamily_at]
  change _ = joinMap _ _ ≫ ((nativeCoherentCone X).val ≫ coherentComparison)
  rw [← Category.assoc, nativeTotCone_cellMap X σ (ULift.up (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0))]
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  rfl

/-- 元の図式に固定すると、全join族は元の同じ指定native錐の全射に戻る。 -/
theorem nativeTotJoinFamily_at (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
      nativeTotJoinFamily A = (nativeDGCone X).val := by
  have hc (n : ℕ)
      (σ : ((SSet.uliftFunctor.{u+1,u}).obj
        (nerve (AsSmall.{u} SimplexCategory))) _⦋n⦌) :=
    nativeTotJoinFamily_at_cell A X σ.down
  have hl := congrArg
    (fun h => joinInl (Δ[0] : SSet.{u+1}) (Δ[0] : SSet.{u+1}) ≫ h)
    (hc 0 (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj ⦋0⦌))))
  simp only [← Category.assoc, joinInl_joinMap, Category.id_comp] at hl
  exact nativeTotJoin_cell_ext hl hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

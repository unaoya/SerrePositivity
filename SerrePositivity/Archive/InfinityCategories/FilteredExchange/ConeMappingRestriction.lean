module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeMappingSpace
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SliceRestrictionRightFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.VertexFiberMapLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：任意の単射な部分形状への頂点固定の錐空間の制限は Kan fibration。
方針：像への同型で slice 制限の right fibration 性を移し、頂点 fiber に制限する。
規約：元の図式・頂点を保持。使われ方：形状の接着の厳密な引き戻しを空間の極限にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet MorphismProperty HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の単射な部分形状への slice 制限は right fibration。 -/
lemma sliceOverRestrict_rightFibration_of_mono {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (i : L ⟶ K) [Mono i] : RightFibration (sliceOverRestrict p i) := by
  let R : K.Subcomplex := Subfunctor.range i
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono i
  have : IsIso (sliceOverRestrict (R.ι ≫ p) (Subfunctor.toRange i)) :=
    sliceOverRestrict_isIso _ _
  have hr := sliceOverRestrict_subcomplex_rightFibration p R
  have he : i = Subfunctor.toRange i ≫ R.ι := rfl
  rw [he, sliceOverRestrict_comp]
  exact ⟨rightFibrations.comp_mem _ _ hr.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- slice 制限の right fibration 性は同じ指定頂点の fiber 上にも誘導される。 -/
lemma coneMappingSpace_restrict_rightFibration {K L X : SSet.{u}} (p : K ⟶ X)
    (i : L ⟶ K) [RightFibration (sliceOverRestrict p i)] (x : X _⦋0⦌) :
    RightFibration (coneRestrictionFiberMap p i x) :=
  HomotopyLimits.vertexFiberMap_rightFibration _ _ _ _ x

/-- 単射な部分形状への固定頂点の錐空間の制限は全ホーンを持ち上げる。 -/
lemma coneMappingSpace_restrict_fibration {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (i : L ⟶ K) [Mono i] (x : X _⦋0⦌) :
    Fibration (coneRestrictionFiberMap p i x) := by
  have := sliceOverRestrict_rightFibration_of_mono p i
  have := coneMappingSpace_restrict_rightFibration p i x
  exact rightFibration_fibration_of_kanComplex _

end SerrePositivity.InfinityCategories.F2

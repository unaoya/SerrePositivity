module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters

/-!
概要：固定辺に付く錐の族から、関手単体集合内の実際の正方形を構成する。
方針：join の円筒比較を curry し、固定辺・恒等辺・二つの写像族の四辺を回収する。
規約：パラメータは任意の単体集合。使われ方：元の前合成を任意の族で認識する合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {T E : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ E) (y : E _⦋0⦌)

/-- 元の錐の族と固定辺を保持した、関手単体集合内の正方形。 -/
def edgeCosliceFamilySquare (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom T).obj E :=
  curry ((β_ T ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] T ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceUncurry e y a)

/-- 正方形の下辺は、元の固定辺を定値関手の族として表す。 -/
lemma edgeCosliceFamilySquare_bottom (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y) :
    SSet.ι₀ ≫ edgeCosliceFamilySquare e y a = e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap T E := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  dsimp only [edgeCosliceFamilySquare]
  rw [uncurry_curry]
  have h : (T ◁ SSet.ι₀) ≫ (β_ T ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom =
      (β_ T (Δ[1] : SSet.{u})).hom ≫ (SSet.ι₀ ▷ T) := by rfl
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.ι₀ ▷ T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] T), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceUncurry_inl]
  rw [uncurry_natural_left]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap]
  rw [uncurry_curry]
  rfl

/-- 正方形の上辺は、元の指定終点における恒等辺である。 -/
lemma edgeCosliceFamilySquare_top (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y) :
    SSet.ι₁ ≫ edgeCosliceFamilySquare e y a =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : T ⟶ E)) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  dsimp only [edgeCosliceFamilySquare]
  rw [uncurry_curry]
  have h : (T ◁ SSet.ι₁) ≫ (β_ T ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom =
      (β_ T (Δ[1] : SSet.{u})).hom ≫ (SSet.ι₁ ▷ T) := by rfl
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.ι₁ ▷ T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] T), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceUncurry_inr, SSet.comp_const, SSet.comp_const]
  rfl

/-- 正方形の二側面は、元の両端点への区間写像空間の族に一致する。 -/
lemma edgeCosliceFamilySquare_side (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y)
    (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] : SSet.{u}) ≫ edgeCosliceFamilySquare e y a =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y i.rev)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  dsimp only [edgeCosliceFamilySquare]
  rw [uncurry_curry, uncurry_curry]
  change (T ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Δ[1]) ≫ (β_ T ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] T ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceUncurry e y a =
      (β_ T (Δ[1] : SSet.{u})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y i.rev)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap_uncurry]
  have h : (T ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Δ[1]) ≫ (β_ T ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom =
      (β_ T (Δ[1] : SSet.{u})).hom ≫
        lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (fst Δ[1] T))
          (snd Δ[1] T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (stdSimplex.δ i.rev) (𝟙 T) := by
    fin_cases i <;> rfl
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (stdSimplex.δ i.rev) (𝟙 T))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] T), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

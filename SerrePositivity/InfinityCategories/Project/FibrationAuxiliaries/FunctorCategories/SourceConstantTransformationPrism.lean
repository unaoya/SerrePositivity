module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism

/-!
概要：定値始域からの変換の空間を、図式を固定した円柱の族で表示する。
方針：内部 Hom の二回の curry と直積の結合子を使う。
規約：元の図式・頂点を全パラメータで厳密に固定する。
使われ方：native な錐空間と定値始域の変換空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：定値始域からの変換の族を元の図式上の円柱に展開する。
方針：区間の族を内部 Hom から評価し、因子を結合し直す。
規約：K・区間・追加パラメータの順。使われ方：全パラメータでの比較。 -/
def sourceConstantTransformationPrism
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X :=
  (α_ K Δ[1] T).hom ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a)

/-- 概要：変換の円柱の始点は指定頂点に定値。
方針：区間写像空間の始点の式を uncurry する。
規約：追加パラメータは忘れる。使われ方：錐の固定図式の確認。 -/
lemma sourceConstantTransformationPrism_zero
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) :
    (SSet.ι₀ ▷ T) ≫ sourceConstantTransformationPrism a = SSet.const z := by
  change (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 T) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a) = _
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]

/-- 変換の円柱の終点は元の図式。 -/
lemma sourceConstantTransformationPrism_one
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) :
    (SSet.ι₁ ▷ T) ≫ sourceConstantTransformationPrism a = fst K T ≫ f := by
  change (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T) ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a) = _
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：両端を固定した円柱の族を定値始域からの変換空間へ戻す。
方針：円柱を二度 curry し、二端の式を区間模型の固定条件に使う。
規約：元の全円柱を保存する。使われ方：native 錐からの比較射。 -/
def sourceConstantTransformationCurry (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X)
    (h₀ : (SSet.ι₀ ▷ T) ≫ R = SSet.const z)
    (h₁ : (SSet.ι₁ ▷ T) ≫ R = fst K T ≫ f) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  let q := curry ((α_ K (Δ[1] : SSet.{u}) T).inv ≫ R)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints q
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]
    change ((K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 T) ≫ (α_ K Δ[1] T).inv) ≫ R = _
    exact h₀
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    change ((K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T) ≫ (α_ K Δ[1] T).inv) ≫ R = _
    exact h₁

/-- 概要：円柱を変換へ戻して展開すると元の円柱に一致する。
方針：区間の curry と内部 Hom の curry の往復、結合子の往復を消す。
規約：全次数での厳密な一致。使われ方：比較射の全族の追跡。 -/
lemma sourceConstantTransformationPrism_curry (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X)
    (h₀ : (SSet.ι₀ ▷ T) ≫ R = SSet.const z)
    (h₁ : (SSet.ι₁ ▷ T) ≫ R = fst K T ≫ f) :
    sourceConstantTransformationPrism (sourceConstantTransformationCurry R h₀ h₁) = R := by
  rw [sourceConstantTransformationPrism, sourceConstantTransformationCurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints, uncurry_curry, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

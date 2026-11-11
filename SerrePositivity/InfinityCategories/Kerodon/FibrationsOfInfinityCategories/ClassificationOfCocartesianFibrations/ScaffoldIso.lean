module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldInverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportInclusion

/-!
概要：cocartesian strict transport への変換空間と水平辺を保つ scaffold Hom の厳密な同型。
方針：両側を元の全 section・全相対 Hom に含め、元の scaffold の二つの往復を使う。
規約：順方向は同じ scaffold 評価であり、全次数の実際の射の同型を与える。
使われ方：cocartesian strict transport の写像空間比較の二対三則。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- cocartesian section の包含後の scaffold 評価は、元の全 section の scaffold 評価。 -/
lemma cocartesianDiagramScaffoldMap_inclusion {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion q) F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldRawMap F q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, η⟩
  rfl

/-- cocartesian scaffold の逆射は、包含後に元の scaffold の逆射と一致する。 -/
lemma cocartesianDiagramScaffoldInverse_inclusion {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceInverse F q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion q) F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFunctorInclusion F q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingHom_ext
  intro c
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldInverseComponent_app_ι F q c n k v α x

/-- 水平辺を保つ scaffold Hom で、逆比較と評価の合成は元の恒等射。 -/
lemma cocartesianDiagramScaffoldInverse_map {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceInverse F q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceMap F q = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFunctorInclusion F q)).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceInverse F q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldRawMap F q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFunctorInclusion F q
  rw [← cocartesianDiagramScaffoldMap_inclusion, ← Category.assoc,
    cocartesianDiagramScaffoldInverse_inclusion, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse_map, Category.comp_id]

/-- strict transport への変換空間で、評価と逆比較の合成は元の恒等射。 -/
lemma cocartesianDiagramScaffoldMap_inverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceMap F q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceInverse F q =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q)) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion q) F)).1
  rw [Category.assoc, cocartesianDiagramScaffoldInverse_inclusion, ← Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldRawMap F q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q =
    𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPost (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion q) F
  rw [← cocartesianDiagramScaffoldMap_inclusion, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap_inverse, Category.comp_id, Category.id_comp]

/-- cocartesian section への全変換と水平辺を保つ scaffold Hom の元の評価による厳密な同型。 -/
def cocartesianDiagramScaffoldMappingIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffoldFunctorSpace F q where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceMap F q
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceInverse F q
  hom_inv_id := cocartesianDiagramScaffoldMap_inverse F q
  inv_hom_id := cocartesianDiagramScaffoldInverse_map F q

/-- 標的が inner fibration のとき、cocartesian strict transport への変換空間は quasicategory。 -/
instance strictDiagramMappingSpace_cocartesianStrictTransport_quasicategory
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {D : SSet.{u}}
    (q : D ⟶ nerve C) [InnerFibration q] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q)) where
  hornFilling' _ _ σ h0 hn := by
    let e := cocartesianDiagramScaffoldMappingIso F q
    obtain ⟨H, hH⟩ := Quasicategory.hornFilling h0 hn (σ ≫ e.hom)
    refine ⟨H ≫ e.inv, ?_⟩
    rw [← Category.assoc, ← hH, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- 同じ scaffold 評価は、inner fibration を標的とすると quasicategory の同値。 -/
lemma cocartesianDiagramScaffoldMappingSpaceMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {D : SSet.{u}}
    (q : D ⟶ nerve C) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianDiagramScaffoldMappingSpaceMap F q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (cocartesianDiagramScaffoldMappingIso F q)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

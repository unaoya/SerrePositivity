module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SlicePrismTriangleEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
/-! # 一定位相の slice prism の全三角形退化

概要：位相に依存しない slice prism の全三角形は、始頂点を重複する退化二単体に一致する。
方針：標準 join 同型の退化自然性と、全パラメーターの join 比較を接続する。
規約：三辺だけでなく同じ二単体族全体を保持する。
使われ方：D の coherent 第一単位則を正本の標準単位三角形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingJoinEdgePoint_unit_degeneracy :
    stdSimplex.σ (0 : Fin 2) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.σ (0 : Fin 1)) (𝟙 (Δ[0] : SSet.{u})) := by
  have he : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.σ (0 : Fin 1))) =
      (stdSimplex.σ (0 : Fin 2) : (Δ[2] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality (SimplexCategory.σ (0 : Fin 1))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.σ (0 : Fin 1)) (𝟙 (Δ[0] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.σ (0 : Fin 1))) at hn
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    hn,
    Iso.inv_hom_id_assoc, he]

lemma dgGluingSlicePrismTriangle_left_degeneracy {K X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⟶ X} (a : (Δ[0] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle ((stdSimplex.σ (0 : Fin 1) ▷ K) ≫ a) =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismEdgeFamily a := by
  symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismEdgeFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, ← Category.assoc, ← comp_whiskerRight,
    dgGluingJoinEdgePoint_unit_degeneracy, comp_whiskerRight, Category.assoc,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison_left
      (Δ[1] : SSet.{u}) Δ[0] K (stdSimplex.σ (0 : Fin 1))]

lemma dgGluingSlicePrismTriangle_constant {K X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⟶ X} (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (snd (Δ[1] : SSet.{u}) K ≫ a) =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a := by
  have he : snd (Δ[1] : SSet.{u}) K ≫ a =
      (stdSimplex.σ (0 : Fin 1) ▷ K) ≫ snd (Δ[0] : SSet.{u}) K ≫ a := rfl
  rw [he, dgGluingSlicePrismTriangle_left_degeneracy,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismEdgeFamily_constant]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

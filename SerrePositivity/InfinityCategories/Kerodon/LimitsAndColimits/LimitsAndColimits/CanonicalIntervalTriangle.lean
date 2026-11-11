module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismEvaluation

/-!
概要：標準の右区間比較の終点側三角形は退化する。
方針：右 join の円筒写像を有限頂点の座標で計算する。
規約：任意の区間図式が標準比較の像にあるとは仮定しない。
使われ方：Ind-S (9) の追加全対角回収条項の像条件の検査。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 標準右区間 prism の終点側三角形は、終点を重複する退化辺。 -/
lemma rightMappingSpacePrism_target_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom =
      stdSimplex.σ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  rw [show SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1) = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex 1).val from
    (SSet.yonedaEquiv.apply_symm_apply _)]
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  let b : (Δ[0] : SSet.{u}) _⦋2⦌ := stdSimplex.objEquiv.symm
    (SimplexCategory.const ⦋2⦌ ⦋0⦌ 0)
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom.app (Opposite.op ⦋2⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[1] Δ[0]).app (Opposite.op ⦋2⦌)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex 1).val.2, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex 1).val.1), b))) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val]
  fin_cases i <;> rfl

/-- 標準右区間比較の像では、終点側三角形は必ず一番退化の像に入る。 -/
lemma pinchedIntervalFamily_target_triangle_degenerate {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    ∃ e : (Δ[1] : SSet.{u}) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
        stdSimplex.σ (1 : Fin 2) ≫ e := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry]
  refine ⟨stdSimplex.δ (1 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f, ?_⟩
  have hh := rightMappingSpacePrism_target_triangle.{u} =≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

module

public import SerrePositivity.KST.LocalizingInvariants.CoherentCompositionConstantSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFixedTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSquareEvaluation

/-!
概要：豊穣合成三角形の通常の射での制限は、元の通常の合成二単体そのものである。
方針：四角形の切断座標を延長した面写像に同定し、定値合成二単体の計算に戻す。
規約：二単体の全豊穣作用を保持。使われ方：後合成 prism の両端と標準三角形の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma coherentCompositionFixedTriangle_vertex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{max u v}))
      (SSet.const (ULift.up (SimplicialCategory.homEquiv' X Y f))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedTriangle X Y Z g) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex := by
  let st := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{max u v} 0)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedTriangle, ← Category.assoc, SSet.yonedaEquiv_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle X Y Z).app (Opposite.op ⦋2⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[2] : SSet.{max u v})),
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 2),
       ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' Y Z g) 2))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle]
  simp only [NatTrans.comp_app, types_comp_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSquare X Y Z).app (Opposite.op ⦋2⦌)
    (st.1, (st.2,
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 2),
       ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' Y Z g) 2)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSquare_evaluate_cut]
  have hc : SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (stdSimplex.objEquiv st.1).toOrderHom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (2 : Fin 3)) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  have ht : (stdSimplex.objEquiv st.2).toOrderHom.comp
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom = (OrderHom.id : Fin 2 →o Fin 2) := by
    ext i
    fin_cases i <;> rfl
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback, ht]
  exact coherentComposition_constant_simplex f g

end SerrePositivity.KST.LocalizingInvariants

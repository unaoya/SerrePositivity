module

public import SerrePositivity.KST.Spectra.WeightedConeTriangleTrace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ReflectedPathCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-!
概要：weighted cone の三角形の経路を、元の係数単体と edgewise 解像の左辺で計算する。
方針：反転 Yoneda の評価式と標準単体の反転同型の逆を相殺する。
規約：反転した係数の元の零・一単体の順序を保持。使われ方：元の評価錐の全体の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 反転係数の simplex を元の標準単体で読むと、その同じ係数の基礎 simplex に戻る。 -/
lemma reflectedCoefficient_unreverse {X : SSet.{u}} {n : ℕ} (τ : Δ[n] ⟶ X.op) :
    (stdSimplex.opIso ⦋n⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap τ =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv τ)) := by
  have hτ : τ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv τ) :=
    (Equiv.symm_apply_apply _ _).symm
  calc
    _ = (stdSimplex.opIso ⦋n⦌).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv τ)) := by
      exact congrArg (fun f ↦ (stdSimplex.opIso ⦋n⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap f) hτ
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reflectedYonedaMap, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- weighted cone の元の三角形の経路は、終点の元の係数一単体の Yoneda 射。 -/
lemma weightedConeSimplex_triangleTrace_yoneda {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) (x : C)
    {σ : ComposableArrows I 1}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 1 ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    triangleTrace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ) =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv (τ.app (1 : Fin 2)))) := by
  rw [weightedConeSimplex_triangleTrace, reflectedCoefficient_unreverse]
  rfl

/-- edgewise 左射影の係数を元の区間に戻すと、元の解像単体の左辺の制限そのもの。 -/
lemma edgewiseLeft_coefficient_unreverse {X : SSet.{u}}
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋1⦌) :
    (stdSimplex.opIso ⦋1⦌).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X).app (Opposite.op ⦋1⦌) a)) =
      (stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}).op Δ[1] ≫ a := by
  rw [reflectedCoefficient_unreverse, Equiv.apply_symm_apply]
  change SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.opObjEquiv.symm
    (SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ a)))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates

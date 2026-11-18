module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeTailComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeOverDiagram

/-!
概要：元の大域 slice 図式の各実単体は、通常 augmentation の同じ終端付き列の join 表示。
方針：先端を除く面を join の自然性で計算し、全末尾単体の厳密な一致を使う。
規約：HA Construction 1.3.1.13、全次数の元の列を保持する。使われ方：元の通常余錐との大域比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverDiagram_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ((strictRawModuleTensorDoubleConeOverDiagram A X P Q).app (Opposite.op ⦋n⦌) c).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
          (strictRawModuleTensorElementAugmentedColumn A X P Q c)) := by
  change (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm
        (strictRawModuleTensorDoubleConeOverSimplex A X P Q c)))).val = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr,
    SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2)))) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
        (strictRawModuleTensorDoubleConeSimplex A X P Q c)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  have hδ : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom =
      (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    change (0 : Fin (n + 2)).succAbove i = i.succ
    rw [Fin.succAbove_zero]
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin (n + 2)))).op
      (strictRawModuleTensorDoubleConeSimplex A X P Q c) = strictRawModuleTensorDoubleConeTail A X P Q c := by
    change (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom
        (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom) = _
    rw [hδ]
    rfl
  rw [hs, strictRawModuleTensorDoubleConeTail_eq_closed]

end SerrePositivity.EInfinity.BarrattEccles

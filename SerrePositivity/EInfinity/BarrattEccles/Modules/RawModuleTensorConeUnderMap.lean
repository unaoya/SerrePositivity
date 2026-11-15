module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeUnderSimplex

/-!
概要：元の反対要素圏の全単体の実 cone を、同じ probe 下の大域 coslice 写像へ束ねる。
方針：点と標準単体の join の自然性と、元の実 cone 単体の全自然性を使う。
規約：添字圏の始対象性は仮定しない。使われ方：同じ実 cone/prism と元の屋根の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeUnderMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorConePoint A X P) where
  app _ := ↾fun c => strictRawModuleTensorConeUnderSimplex A X P Q c
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
          (strictRawModuleTensorConeSimplex A X P Q
            ((nerve (strictRawModuleTensorElementIndex A X P Q)).map α c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α.unop) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
            (strictRawModuleTensorConeSimplex A X P Q c))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left]
    have hn := strictRawModuleTensorConeSimplex_naturality A X P Q c α.unop
    exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n.unop.len + 1) =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm s) hn

lemma strictRawModuleTensorConeUnderMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeUnderMap A X P Q).app (Opposite.op ⦋n⦌) c =
      strictRawModuleTensorConeUnderSimplex A X P Q c := rfl

end SerrePositivity.EInfinity.BarrattEccles

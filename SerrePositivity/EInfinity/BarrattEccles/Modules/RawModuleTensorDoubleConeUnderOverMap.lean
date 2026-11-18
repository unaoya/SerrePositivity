module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeUnderOverSimplex

/-!
概要：同じ終端 X 上の slice 内で、元の全二重 cone 単体を大域 coslice 写像へ束ねる。
方針：始点付き全作用素の自然性と、点と標準単体の join の自然性を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、同じ元の要素圏・恒等錐を保持する。使われ方：大域二重 join。
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

def strictRawModuleTensorDoubleConeUnderOverMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorIdentityOverPoint A X P) where
  app _ := ↾fun c => strictRawModuleTensorDoubleConeUnderOverSimplex A X P Q c
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm
          (strictRawModuleTensorDoubleConeOverSimplex A X P Q
            ((nerve (strictRawModuleTensorElementIndex A X P Q)).map α c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α.unop) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm
            (strictRawModuleTensorDoubleConeOverSimplex A X P Q c))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left]
    have hn := strictRawModuleTensorDoubleConeOverSimplex_naturality A X P Q c α.unop
    exact congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)) _⦋n.unop.len + 1⦌ =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm s) hn

lemma strictRawModuleTensorDoubleConeUnderOverMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeUnderOverMap A X P Q).app (Opposite.op ⦋n⦌) c =
      strictRawModuleTensorDoubleConeUnderOverSimplex A X P Q c := rfl

end SerrePositivity.EInfinity.BarrattEccles

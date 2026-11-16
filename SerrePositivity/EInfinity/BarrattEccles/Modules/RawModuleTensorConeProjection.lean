module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeUnderMap

/-!
概要：元の大域 coslice 写像の射影は、同じ元の通常 frame 図式の閉 nerve である。
方針：join の右包含を最初の面へ戻し、同じ cone 単体の通常末尾面を回収する。
規約：元の全通常図式を厳密に保持する。使われ方：同じ実 cone と屋根評価の比較。
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

def strictRawModuleTensorElementNerveDiagram :
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) :=
  nerveMap (strictRawModuleTensorElementDiagram A X P Q ⋙
    ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) ≫
      strictRawModuleDGSource A X

lemma strictRawModuleTensorElementNerveDiagram_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementNerveDiagram A X P Q).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q) := rfl

lemma strictRawModuleTensorConeUnderMap_projection :
    strictRawModuleTensorConeUnderMap A X P Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (strictRawModuleTensorConePoint A X P) =
      strictRawModuleTensorElementNerveDiagram A X P Q := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
        (strictRawModuleTensorConeSimplex A X P Q c))) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr,
    SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change (strictRawModuleTensorConeSimplex A X P Q c).pullback
    (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = _
  have hδ : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom =
      (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    change (0 : Fin (n + 2)).succAbove i = i.succ
    rw [Fin.succAbove_zero]
  rw [hδ]
  exact strictRawModuleTensorConeSimplex_tail A X P Q c

end SerrePositivity.EInfinity.BarrattEccles

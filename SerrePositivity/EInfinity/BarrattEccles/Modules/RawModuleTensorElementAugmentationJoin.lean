module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementAugmentedColumn
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeUnderSimplex

/-!
概要：元の通常 augmentation の全余錐 join と同じ通常円柱を回収する。
方針：同じ宇宙の元の余錐へ既存の全 prism 比較を適用し、同じ dg 源へ送る。
規約：HA Construction 1.3.1.13、元の全列と同じ分解を保持する。
使われ方：同じ slice 評価と元の全 augmentation 同型の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma ordinaryCoconeRestriction {I C : Type (u + 1)}
    [Category.{u + 1} I] [Category.{u + 1} C] {F : I ⥤ C}
    (c : CategoryTheory.Limits.Cocone F) {n : ℕ} (Γ : ComposableArrows I n)
    {T : SSet.{u + 1}} (G : nerve C ⟶ T) :
    joinMap (SSet.yonedaEquiv.symm Γ) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      ((nerveCoconeEquiv c).val ≫ G) =
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (G.app (Opposite.op ⦋n + 1⦌) (diagram c Γ)) := by
  calc
    _ = (joinMap (SSet.yonedaEquiv.symm Γ) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        (nerveCoconeEquiv c).val) ≫ G := (Category.assoc _ _ _).symm
    _ = ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm (diagram c Γ)) ≫ G :=
      congrArg (fun f => f ≫ G) (diagram_join c Γ).symm
    _ = (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv.symm (diagram c Γ) ≫ G) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => (joinStdSimplexIso n 0).hom ≫ f)
      (SSet.yonedaEquiv_symm_comp (diagram c Γ) G)

def strictRawModuleTensorElementAugmentationJoin :
    join (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[0] : SSet.{u + 1}) ⟶
      dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X)) :=
  (nerveCoconeEquiv (strictRawModuleTensorElementAugmentationCocone A X P Q)).val ≫
    strictRawModuleDGSource A X

lemma strictRawModuleTensorElementAugmentationJoin_inr :
    joinInr (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[0] : SSet.{u + 1}) ≫
      strictRawModuleTensorElementAugmentationJoin A X P Q = strictRawModuleTensorConePoint A X P := by
  rw [strictRawModuleTensorElementAugmentationJoin, ← Category.assoc, nerveCocone_point]
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm
      (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj ((strictRawModuleProbeFunctor A X).obj P))) ≫
      strictRawModuleDGSource A X) = _
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hp := (SSet.yonedaEquiv (X := dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X)))
    (n := ⦋0⦌)).apply_symm_apply
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A
        (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))
  exact (strictRawModuleDGSource_vertex A X
    ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj ((strictRawModuleProbeFunctor A X).obj P))).trans hp.symm

lemma strictRawModuleTensorElementAugmentationJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      strictRawModuleTensorElementAugmentationJoin A X P Q =
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (closedNerveSimplex (strictRawModuleTensorElementAugmentedColumn A X P Q c)) := by
  have h := ordinaryCoconeRestriction
    (strictRawModuleTensorElementAugmentationCocone A X P Q) c (strictRawModuleDGSource A X)
  have he : (strictRawModuleDGSource A X).app (Opposite.op ⦋n + 1⦌)
      (diagram (strictRawModuleTensorElementAugmentationCocone A X P Q) c) =
      closedNerveSimplex (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (strictRawModuleTensorElementAugmentedColumn A X P Q c) := rfl
  exact h.trans (congrArg (fun e :
      (dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X))) _⦋n + 1⦌ =>
        (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm e) he)

lemma strictRawModuleTensorElementAugmentationJoin_prism_source :
    (β_ (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[1] : SSet.{u + 1})).hom ≫
      rightMappingSpacePrism _ ≫ strictRawModuleTensorElementAugmentationJoin A X P Q ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
      (strictRawModuleDiagramNatTransHomotopy A X
        (strictRawModuleTensorElementAugmentation A X P Q)).h := by
  have h := nerveCoconePrism_eq_natTrans
    (strictRawModuleTensorElementDiagram A X P Q ⋙
      ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))
    (strictRawModuleTensorElementAugmentationCocone A X P Q)
  have hη : (strictRawModuleTensorElementAugmentationCocone A X P Q).ι =
      CategoryTheory.Functor.whiskerRight (strictRawModuleTensorElementAugmentation A X P Q)
        (ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) := rfl
  have hraw := congrArg (fun η :
      (strictRawModuleTensorElementDiagram A X P Q ⋙
        ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
        ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj ((strictRawModuleProbeFunctor A X).obj P)) =>
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η).h) hη
  have hp := congrArg (fun f => f ≫ strictRawModuleSource A X) (h.trans hraw)
  change _ = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
    (CategoryTheory.Functor.whiskerRight (strictRawModuleTensorElementAugmentation A X P Q)
      (ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)))).h ≫
        strictRawModuleSource A X
  simpa only [strictRawModuleTensorElementAugmentationJoin, strictRawModuleSource,
    Category.assoc] using hp

end SerrePositivity.EInfinity.BarrattEccles

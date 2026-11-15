module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorLinearAugmentationVertex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAugmentation
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality

/-!
概要：一点選択の元の cochain は、同じ最大点の実 augmentation で恒等 cochain へ戻る。
方針：添字等式の輸送と後合成を両立させ、同じ選択列の一点普遍成分を使う。
規約：元の実辺を保持する。使われ方：二重 cone の三点方程式。
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
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f 0
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)) 0),
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj j))).f 0
        (cast (congrArg (fun z => (GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj z)) 0 : Type u)) h) v) =
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i))).f 0 v := by
    intro i j h v
    subst j
    rfl
  have hcard : J.card = J.card - 1 + 1 := by omega
  have hz := strictRawModuleTensorElementLinear_augmentation_vertex A X P Q
    ((SimplexCategory.toCat.map (strictRawModuleTensorElementSelection J hJ)).toFunctor ⋙ c)
    Finset.univ Finset.univ_nonempty
    (by simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hc)
  exact (ht _ _ (strictRawModuleTensorElementSelection_last J hJ)
    (strictRawModuleTensorElementSelectedCochain A X P Q c J 0 hJ (by omega))).trans hz

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_compose_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).val
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val := by
  rw [modulePostcompose_graded]
  exact strictRawModuleTensorElementSelectedCochainAtMax_augmentation_vertex A X P Q c J hJ hc

end SerrePositivity.EInfinity.BarrattEccles

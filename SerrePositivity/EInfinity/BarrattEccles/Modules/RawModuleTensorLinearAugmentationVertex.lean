module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorLinearAugmentation
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality

/-!
概要：元の普遍 cochain の一点成分は、同じ実 augmentation で元の恒等 cochain に送られる。
方針：元の全線形 augmentation 式を一点集合で評価し、同じ閉頂点の線形値を回収する。
規約：元の実恒等辺を保つ。使われ方：augmentation 三角形の三点 HA 方程式。
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
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app
      (c.obj (Fin.last n)))).f 0
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J 0 hJ (by omega)) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val := by
  let θ := (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) 0 :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (𝟙 ((strictRawModuleProbeFunctor A X).obj P)))
  have hi : Set.InjOn θ (J : Set (Fin (n + 1))) := by
    intro i hi j hj _
    exact (Finset.card_le_one.mp (show J.card ≤ 1 by omega)) i hi j hj
  have himg : J.image θ = (Finset.univ : Finset (Fin 1)) := by
    apply Finset.eq_univ_of_card
    simpa only [Finset.card_image_of_injOn hi, Fintype.card_fin] using hc
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (y := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
    θ s.val J 0 hJ (by omega) hi
  have hp' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback θ s.val).component J 0 hJ (by omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (y := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) s := by
    simpa only [himg, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue] using hp
  have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) n =>
    t.val.component J 0 hJ (by omega))
      (strictRawModuleTensorElementLinear_augmentation A X P Q c)
  exact h.trans (hp'.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_linearValue A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (q := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (y := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) _))

end SerrePositivity.EInfinity.BarrattEccles

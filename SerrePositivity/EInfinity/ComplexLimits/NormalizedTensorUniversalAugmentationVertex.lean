module
public import
  SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalAugmentationLinear
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalLinear_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (homPostcompose X ((normalizedTensorElementAugmentation A X Y).app
      (c.obj (Fin.last n)))).f 0
      ((normalizedTensorElementUniversalLinear A X Y c).val.component J 0 hJ (by omega)) =
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val := by
  let θ := (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X X 0 :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X)))
  have hi : Set.InjOn θ (J : Set (Fin (n + 1))) := by
    intro i hi j hj _
    exact (Finset.card_le_one.mp (show J.card ≤ 1 by omega)) i hi j hj
  have himg : J.image θ = (Finset.univ : Finset (Fin 1)) := by
    apply Finset.eq_univ_of_card
    simpa only [Finset.card_image_of_injOn hi, Fintype.card_fin] using hc
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj (A := A) (D := Complex A) (x := X) (y := X)
    θ s.val J 0 hJ (by omega) hi
  have hp' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback θ s.val).component J 0 hJ (by omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (A := A) (D := Complex A) (x := X) (y := X) s := by
    simpa only [himg, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue] using hp
  have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X X n =>
    t.val.component J 0 hJ (by omega))
      (normalizedTensorElementUniversalLinear_augmentation A X Y c)
  exact h.trans (hp'.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_linearValue A (Complex A) (q := X) (y := X) _))

end SerrePositivity.EInfinity.ComplexLimits

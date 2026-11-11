module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalLinear

/-!
概要：元の全普遍 cochain の面・退化の成分式を与える。
方針：元の線形再添字等式を任意の部分集合で評価し、単射・非単射の分岐を使う。
規約：終端が動く場合の同じ frame 射の後合成を保持する。
使われ方：大域 prism の削除項と退化成分の消滅。
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

lemma normalizedTensorElementUniversalLinear_component_reindex {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((normalizedTensorElementUniversalLinear A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback θ.toOrderHom (normalizedTensorElementUniversalLinear A X Y c).val)
      J k hJ hk := by
  exact (congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X
      ((normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))) m =>
      s.val.component J k hJ hk)
    (normalizedTensorElementUniversalLinear_reindex A X Y c θ)).symm

lemma normalizedTensorElementUniversalLinear_component_inj {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((normalizedTensorElementUniversalLinear A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    (normalizedTensorElementUniversalLinear A X Y c).val.component (J.image θ.toOrderHom) k
      (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk) :=
  (normalizedTensorElementUniversalLinear_component_reindex A X Y c θ J k hJ hk).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj (A := A) (D := Complex A) (x := X)
      (y := (normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)))
      θ.toOrderHom (normalizedTensorElementUniversalLinear A X Y c).val J k hJ hk hi)

lemma normalizedTensorElementUniversalLinear_component_not_inj {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬ Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((normalizedTensorElementUniversalLinear A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) = 0 :=
  (normalizedTensorElementUniversalLinear_component_reindex A X Y c θ J k hJ hk).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj (A := A) (D := Complex A) (x := X)
      (y := (normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)))
      θ.toOrderHom (normalizedTensorElementUniversalLinear A X Y c).val J k hJ hk hi)

end SerrePositivity.EInfinity.ComplexLimits

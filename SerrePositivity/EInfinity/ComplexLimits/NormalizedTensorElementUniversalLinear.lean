module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalSimplexReindex

/-!
概要：全単体列の普遍単体を実 cochain 成分とその微分方程式に移す。
方針：元の pinched 線形表示と全再添字・同じ後合成鎖写像との整合を使う。
規約：全ての有限部分集合と正しい次数を保つ。
使われ方：大域 prism の実高次 cochain と削除・切断方程式。
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

def normalizedTensorElementUniversalLinear {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X ((normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))) n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (normalizedTensorElementUniversalSimplex A X Y c)

lemma normalizedTensorElementUniversalLinear_equation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A ((normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk) =
      (normalizedTensorElementUniversalLinear A X Y c).val.rhs J k hk :=
  (normalizedTensorElementUniversalLinear A X Y c).equation J k hJ hk

lemma normalizedTensorElementUniversalLinear_reindex {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback θ.toOrderHom (normalizedTensorElementUniversalLinear A X Y c) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))
      (normalizedTensorElementUniversalLinear A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := A) (D := Complex A) (x := X)
      (y := (normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))))
    (normalizedTensorElementUniversalSimplex_reindex A X Y c θ)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback (normalizedTensorElementUniversalSimplex A X Y c) θ).symm.trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _))

end SerrePositivity.EInfinity.ComplexLimits

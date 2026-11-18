module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedAtMaxImage
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementPinchedEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPostcomposeGraded

/-!
概要：元の最大点付き選択 cochain の評価を、同じ大域 pinched 族の線形成分へ戻す。
方針：全評価の自然性・Hom 後合成の合成則・元の全単体評価式を使う。
規約：任意次数・非空部分集合・実評価射を保持する。使われ方：大域評価三角形の混合項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_evaluation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)))).f k
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))).f k
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk) := by
  rw [← _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_image A X Y c J k hJ hk]
  have hn := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).naturality
    (c.map (homOfLE (Fin.le_last (J.max' hJ))))
  have hn' : (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)) :=
    hn.trans (Category.comp_id _)
  have hf := (homFunctor X).map_comp
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))
  change homPostcompose X (_ ≫ _) = _ at hf
  rw [hn'] at hf
  exact congrArg (fun f => f.f k
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk)) hf

lemma normalizedTensorElementUniversalLinear_evaluation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap_app]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _).symm

lemma normalizedTensorElementSelectedCochainAtMax_evaluation_pinched {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)))).f k
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X Y n => s.val.component J k hJ hk)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_evaluation A X Y c)
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_evaluation A X Y c J k hJ hk).trans h

lemma normalizedTensorElementSelectedCochainAtMax_evaluation_compose {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ))))).val
      (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) (add_zero k) =
    r • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  rw [_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded]
  simp only [Units.smul_def, map_zsmul,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_evaluation_pinched A X Y c J k hJ hk]

end SerrePositivity.ComplexLimits

module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedAtMaxImage
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementPinchedEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.ComplexPostcomposeGraded

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_evaluation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)))).f k
      (normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (homPostcompose X ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))).f k
      ((normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk) := by
  rw [← normalizedTensorElementSelectedCochainAtMax_image A X Y c J k hJ hk]
  have hn := (normalizedTensorElementEvaluation A X Y).naturality
    (c.map (homOfLE (Fin.le_last (J.max' hJ))))
  have hn' : (normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))) ≫
        (normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)) =
      (normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)) :=
    hn.trans (Category.comp_id _)
  have hf := (homFunctor X).map_comp
    ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))
    ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n)))
  change homPostcompose X (_ ≫ _) = _ at hf
  rw [hn'] at hf
  exact congrArg (fun f => f.f k
    (normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk)) hf

lemma normalizedTensorElementUniversalLinear_evaluation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))))
      (normalizedTensorElementUniversalLinear A X Y c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c) := by
  rw [normalizedTensorElementPinchedMap_app]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _).symm

lemma normalizedTensorElementSelectedCochainAtMax_evaluation_pinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ)))).f k
      (normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A X Y n => s.val.component J k hJ hk)
    (normalizedTensorElementUniversalLinear_evaluation A X Y c)
  exact (normalizedTensorElementSelectedCochainAtMax_evaluation A X Y c J k hJ hk).trans h

lemma normalizedTensorElementSelectedCochainAtMax_evaluation_compose {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
      ((normalizedTensorElementEvaluation A X Y).app (c.obj (J.max' hJ))))).val
      (r • normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) (add_zero k) =
    r • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  rw [complexPostcompose_graded]
  simp only [Units.smul_def, map_zsmul,
    normalizedTensorElementSelectedCochainAtMax_evaluation_pinched A X Y c J k hJ hk]

end SerrePositivity.EInfinity.ComplexLimits

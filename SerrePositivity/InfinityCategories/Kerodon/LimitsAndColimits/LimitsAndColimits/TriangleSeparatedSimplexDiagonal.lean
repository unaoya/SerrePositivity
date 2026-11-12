module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedDirectEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleRightIntervalHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleDiagonalLabels
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderHomNormalization

/-!
概要：再構成単体の長辺は、元の長 Hom の直接評価の標準 coherent 区間単体そのもの。
方針：中間ラベルのない対角では二切断を同じ座標へ戻し、全 Hom を正規化して照合する。
規約：任意の次数の実際の豊穣関手の等号。
使われ方：正規化後の全対角の厳密回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleSeparatedSimplex_diagonal
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
    {K L : SSet.{max u v}}
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v}
        (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    (hdiag : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleParameterDiagonal K L) ≫ M = q)
    {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ L) ≫ q).app (Opposite.op ⦋n⦌) (s, r)).down t := by
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel t
  let d := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ L) ≫ q).app (Opposite.op ⦋n⦌) (s, r)).down
  let hx (i : Fin (n + 1)) (hi : t i = 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s l i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hi)
  let hz (i : Fin (n + 1)) (hi : t i = 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s l i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_two t hi)
  have ho (i : Fin (n + 1)) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r l).obj ⟨ULift.up i⟩ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex d t).obj ⟨ULift.up i⟩ := by
    by_cases hi : t i = 0
    · exact (hx i hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero d t i hi).symm
    · have hi' : t i = 1 := by omega
      exact (hz i hi').trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one d t i hi').symm
  apply EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedSimplex f g M hM s r l)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex d t) (fun i => ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom f g M s r l i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (ho i) (ho j)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex d t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (hx i hi) (hx j hj) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero d t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero d t j hj)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_zero f g M s r l i j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hj),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_zeroHom d t i j hi hj]
    rfl
  · have hj' : t j = 1 := by omega
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (hx i hi) (hz j hj') (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero d t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one d t j hj')
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_long f g M s r l i j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_two t hj'),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleRightIntervalHom d t i j hi hj']
    have hP : ∀ P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j),
        ¬ ∃ k : Fin (n + 1), ULift.up k ∈ P.I ∧ l k = 1 := by
      intro P
      rintro ⟨k, _, hk⟩
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_ne_one t k hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_direct_eq M q hdiag s r l (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hi) hP,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom_at_simplex,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCutMap_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_diagonal t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero l (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_zero t hi)) hi j]
  · have hi' : t i = 1 := by omega
    apply SSet.hom_ext
    intro e
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (P.obj 0)
    have ht := t.monotone hp
    rw [hi', hj] at ht
    omega
  · have hi' : t i = 1 := by omega
    have hj' : t j = 1 := by omega
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (hz i hi') (hz j hj') (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one d t i hi')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one d t j hj')
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_two f g M s r l i j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_two t hi') (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDiagonalLabel_two t hj'),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_oneHom d t i j hi' hj']
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

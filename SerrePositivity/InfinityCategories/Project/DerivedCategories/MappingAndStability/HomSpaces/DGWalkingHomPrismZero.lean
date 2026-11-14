module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComponents

/-! # 固定標的の前合成 prism の零端点

概要：標的だけ相一にした係数単体は、前合成評価で写した元の単体に一致する。
方針：始点は常に相零、標的の自然変換成分は恒等であることを全斉次成分で使う。
規約：全次元の単体の厳密な等式。使われ方：slice prism の始端を閉前合成へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {p q : D} (y : D)
variable (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)

/-- 零相同士の斉次射は、前合成評価で写る。 -/
lemma dgWalkingHomPrecompose_transition_zero
    {a b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)} {i j : Fin 2}
    (hi : i = 0) (hj : j = 0) {k : ℤ} (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A a b k) (h : i ≤ j) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).transition i j h f)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r).map a b).f k f) := by
  subst i
  subst j
  rfl

/-- 標的の恒等成分をまたぐ斉次射は、前合成評価の像そのもの。 -/
lemma dgWalkingHomPrecompose_transition_target
    {a b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)} {i j : Fin 2}
    (hi : i = 0) (hj : j = 1)
    (hb : b = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y)) {k : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A a b k) (h : i ≤ j) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).transition i j h f)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r).map a b).f k f) := by
  subst i
  subst j
  subst b
  exact heq_of_eq (_root_.SerrePositivity.DifferentialGraded.unit_compose A _)

/-- 標的だけ一相の係数単体は、閉前合成の評価で写した単体。 -/
lemma dgWalkingHomPrism_zero {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).simplex s.val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) =
      s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext a
    induction a using Fin.lastCases with
    | last =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2)) (Fin.last (n + 1)))
        (s.val.obj (Fin.last (n + 1))) = _
      exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y) z
          (s.val.obj (Fin.last (n + 1)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last _)).trans
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s)).trans
            (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r).obj
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s)).symm)
    | cast a =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2)) a.castSucc)
        (s.val.obj a.castSucc) = _
      exact congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y) z
          (s.val.obj a.castSucc)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ a)
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card hI
    have haLast : a ≠ Fin.last (n + 1) := ne_of_lt (hab.trans_le (Fin.le_last b))
    obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last haLast
    change HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).transition
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase _ a.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase _ b) _
        (s.val.hom I a.castSucc b k hI ha hb hk)) _
    induction b using Fin.lastCases with
    | last =>
      exact dgWalkingHomPrecompose_transition_target A D y r
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s) _ _
    | cast b =>
      exact dgWalkingHomPrecompose_transition_zero A D y r
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_castSucc _ b) _ _


end SerrePositivity.InfinityCategories.Project.DerivedCategories

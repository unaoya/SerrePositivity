module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFreeLiftPostcomp

/-! # 自由 Hom の評価関手の自然性

概要：自由係数の評価と dg 関手による後合成を厳密に比較する。
方針：自由 lift の再構成から、二対象と唯一の生成辺を照合する。
規約：全 Hom 複体上の関手等式。使われ方：閉細分 prism の商自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]

/-- 自由係数の評価を dg 関手で後合成すると、その Hom 鎖写像で評価される。 -/
lemma dgWalkingHomEvaluation_postcomp (M : Complex A) (q y : D)
    (φ : M ⟶ homObject A D q y) (Q : DGFunctor A D E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D M q y φ).comp Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E M (Q.obj q) (Q.obj y) (φ ≫ Q.map q y) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFreeLift_postcomp]
  congr 1
  · funext x
    rcases x with ⟨x⟩
    cases x <;> rfl
  · apply Function.hfunext rfl
    intro x x' hx
    cases hx
    apply Function.hfunext rfl
    intro y y' hy
    cases hy
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y
    · exact heq_of_eq zero_comp
    · rfl
    · exact heq_of_eq zero_comp
    · exact heq_of_eq zero_comp

/-- 係数鎖写像で自由 Hom を写してから評価すると、合成した係数で評価される。 -/
lemma dgWalkingHomMap_evaluation {M N : Complex A} (θ : M ⟶ N) (q y : D)
    (φ : N ⟶ homObject A D q y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap.{u, v} A θ).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D N q y φ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D M q y (θ ≫ φ) := by
  refine (FreeDGCategory.lift_reconstruction A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A θ).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D N q y φ))).symm.trans ?_
  change FreeDGCategory.lift A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluationObject D q y) _ = _
  congr 1
  funext a b
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  cases a <;> cases b
  · exact (isZero_zero (Complex A)).eq_of_src _ _
  · change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A M ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A θ).map _ _ ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D N q y φ).map _ _) = θ ≫ φ
    let ev := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D N q y φ).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A N)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ ev) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_generator A θ)).trans
        ((Category.assoc θ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A N) ev).trans
          (congrArg (fun f => θ ≫ f)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator A D N q y φ))))
  · exact (isZero_zero (Complex A)).eq_of_src _ _
  · exact (isZero_zero (Complex A)).eq_of_src _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

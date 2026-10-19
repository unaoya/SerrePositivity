module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomMap
public import SerrePositivity.InfinityCategories.Derived.DGFreeLiftPostcomp

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]

/-- 自由係数の評価を dg 関手で後合成すると、その Hom 鎖写像で評価される。 -/
lemma dgWalkingHomEvaluation_postcomp (M : Complex A) (q y : D)
    (φ : M ⟶ homObject A D q y) (Q : DGFunctor A D E) :
    (dgWalkingHomEvaluation A D M q y φ).comp Q =
      dgWalkingHomEvaluation A E M (Q.obj q) (Q.obj y) (φ ≫ Q.map q y) := by
  unfold dgWalkingHomEvaluation
  rw [dgFreeLift_postcomp]
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
    (dgWalkingHomMap.{u, v} A θ).comp (dgWalkingHomEvaluation A D N q y φ) =
      dgWalkingHomEvaluation A D M q y (θ ≫ φ) := by
  refine (FreeDGCategory.lift_reconstruction A DGWalkingHomVertex D
    (dgWalkingHomQuiver A M)
    ((dgWalkingHomMap A θ).comp (dgWalkingHomEvaluation A D N q y φ))).symm.trans ?_
  change FreeDGCategory.lift A DGWalkingHomVertex D (dgWalkingHomQuiver A M)
    (dgWalkingHomEvaluationObject D q y) _ = _
  congr 1
  funext a b
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  cases a <;> cases b
  · exact (isZero_zero (Complex A)).eq_of_src _ _
  · change dgWalkingHomGenerator A M ≫
      ((dgWalkingHomMap A θ).map _ _ ≫
        (dgWalkingHomEvaluation A D N q y φ).map _ _) = θ ≫ φ
    let ev := (dgWalkingHomEvaluation A D N q y φ).map
      (dgWalkingHomSource A N) (dgWalkingHomTarget A N)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ ev) (dgWalkingHomMap_generator A θ)).trans
        ((Category.assoc θ (dgWalkingHomGenerator A N) ev).trans
          (congrArg (fun f => θ ≫ f)
            (dgWalkingHomEvaluation_generator A D N q y φ))))
  · exact (isZero_zero (Complex A)).eq_of_src _ _
  · exact (isZero_zero (Complex A)).eq_of_src _ _

end SerrePositivity.InfinityCategories

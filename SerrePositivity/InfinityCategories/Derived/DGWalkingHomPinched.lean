module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition

/-! # 全次数の pinched Hom の自由係数表示

概要：自由 Hom の生成辺に全 pinched 単体を含め、評価による全次数の回収を証明する。
方針：生成辺の評価公式を pinched Hom 鎖写像の合成公式へ移す。
規約：頂点だけでなく単体集合の射の等式。使われ方：閉前合成 prism の両端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A]

/-- 元の Hom の全次数の単体を、自由係数 dg 圏の指定 Hom に含める。 -/
def dgWalkingHomPinched (D : Type v) [DGCategory A D] (q y : D) :
    DGNerve.pinchedHom A D q y ⟶
      DGNerve.pinchedHom A (DGWalkingHom.{u, v} A (homObject A D q y))
        (dgWalkingHomSource A (homObject A D q y))
        (dgWalkingHomTarget A (homObject A D q y)) :=
  pinchedHomChainMap (dgWalkingHomGenerator A (homObject A D q y))

/-- dg 関手の Hom 鎖写像は、全単体の元の dg nerve の像を保つ。 -/
lemma dgFunctorPinchedChainMap_val {C D : Type v} [DGCategory A C] [DGCategory A D]
    (F : DGFunctor A C D) {x y : C} {n : ℕ}
    (s : (DGNerve.pinchedHom A C x y).obj (Opposite.op ⟨n⟩)) :
    ((pinchedHomChainMap (F.map x y)).app (Opposite.op ⟨n⟩) s).val = s.val.map F := by
  have h := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (dgFunctor_pinchedHomMap_eq F x y)
  exact h.symm.trans (pinchedEndpointIso_hom_val _ _ _)

/-- 自由係数を任意の Hom 鎖写像で評価すると、その鎖写像の全 pinched 作用を回収する。 -/
lemma dgWalkingHomPinched_evaluation (D E : Type v) [DGCategory A D] [DGCategory A E]
    (q y : D) (q' y' : E) (φ : homObject A D q y ⟶ homObject A E q' y') :
    dgWalkingHomPinched A D q y ≫
      pinchedHomChainMap ((dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ).map
        (dgWalkingHomSource A (homObject A D q y))
        (dgWalkingHomTarget A (homObject A D q y))) = pinchedHomChainMap φ := by
  rw [dgWalkingHomPinched, ← pinchedHomChainMap_comp, dgWalkingHomEvaluation_generator]

/-- 恒等評価は、元の pinched Hom 全体の恒等射を回収する。 -/
lemma dgWalkingHomPinched_identity (D : Type v) [DGCategory A D] (q y : D) :
    dgWalkingHomPinched A D q y ≫
      pinchedHomChainMap ((dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)).map
        (dgWalkingHomSource A (homObject A D q y))
        (dgWalkingHomTarget A (homObject A D q y))) = 𝟙 _ := by
  rw [dgWalkingHomPinched_evaluation, pinchedHomChainMap_id]

/-- 閉前合成による評価は、その元の全次数の前合成射を回収する。 -/
lemma dgWalkingHomPinched_precomposition (D : Type v) [DGCategory A D] [Small.{u} D]
    {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgWalkingHomPinched A D q y ≫
      pinchedHomChainMap ((dgWalkingHomEvaluation A D (homObject A D q y) p y
        (dgClosedPrecomposition A D r)).map
          (dgWalkingHomSource A (homObject A D q y))
          (dgWalkingHomTarget A (homObject A D q y))) =
      pinchedClosedPrecomposition A D r :=
  dgWalkingHomPinched_evaluation A D D q y p y (dgClosedPrecomposition A D r)

/-- 自由係数単体の評価は、元の係数鎖写像による全単体の像そのもの。 -/
lemma dgWalkingHomPinched_evaluation_val (D E : Type v) [DGCategory A D] [DGCategory A E]
    (q y : D) (q' y' : E) (φ : homObject A D q y ⟶ homObject A E q' y') {n : ℕ}
    (s : (DGNerve.pinchedHom A D q y).obj (Opposite.op ⟨n⟩)) :
    ((dgWalkingHomPinched A D q y).app (Opposite.op ⟨n⟩) s).val.map
      (dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ) =
      ((pinchedHomChainMap φ).app (Opposite.op ⟨n⟩) s).val := by
  have h := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (dgWalkingHomPinched_evaluation A D E q y q' y' φ)
  exact (dgFunctorPinchedChainMap_val A
    (dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ)
      ((dgWalkingHomPinched A D q y).app (Opposite.op ⟨n⟩) s)).symm.trans h

end SerrePositivity.InfinityCategories

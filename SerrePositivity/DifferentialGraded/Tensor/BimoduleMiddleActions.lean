module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # 中間圏のtensor比較と外側の両dg作用の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

lemma middleRestrictionComparisonValue_rightAction (b b' : Bᵒᵖ) (d : D) (e : E)
    {p k r i j n : ℤ} (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A b b' p) (q : (Q.value (F.obj d) e).X k)
    (v : (P.value b.unop (F.obj d)).X r) :
    (middleRestrictionComparisonValue A B C D E F P Q b'.unop e).f n
      (moduleAction A ((compose A B D E (Bimodule.leftRestriction A B C D F P)
          (Bimodule.rightRestriction A C D E F Q)).rightAt e) g
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b.unop) d q v ha) hn) =
    moduleAction A ((compose A B C E P Q).rightAt e) g
      ((middleRestrictionComparisonValue A B C D E F P Q b.unop e).f i
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b.unop) d q v ha)) hn := by
  rw [compose_rightAction_element A B D E _ _ b b' d e ha hj hn]
  simp only [Units.smul_def, map_zsmul]
  rw [middleRestrictionComparisonValue_element, middleRestrictionComparisonValue_element,
    compose_rightAction_element A B C E P Q b b' (F.obj d) e ha hj hn]
  rfl

lemma middleRestrictionComparisonValue_leftAction (b : B) (d : D) (e e' : E)
    {p k r i j n : ℤ} (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value (F.obj d) e).X k)
    (v : (P.value b (F.obj d)).X r) :
    (middleRestrictionComparisonValue A B C D E F P Q b e').f n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B D E (Bimodule.leftRestriction A B C D F P)
          (Bimodule.rightRestriction A C D E F Q)).leftAt b) g
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q v ha) hn) =
    SerrePositivity.DifferentialGraded.leftAction A ((compose A B C E P Q).leftAt b) g
      ((middleRestrictionComparisonValue A B C D E F P Q b e).f i
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q v ha)) hn := by
  rw [compose_leftAction_element A B D E _ _ b d e e' ha hj hn,
    Bimodule.rightRestriction_leftAction,
    middleRestrictionComparisonValue_element, middleRestrictionComparisonValue_element,
    compose_leftAction_element A B C E P Q b (F.obj d) e e' ha hj hn]

lemma middleRestrictionComparisonValue_right_naturality (b b' : Bᵒᵖ) (e : E) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e).map b b' ≫
      homPostcompose _ (middleRestrictionComparisonValue A B C D E F P Q b'.unop e) =
    ((compose A B C E P Q).rightAt e).map b b' ≫
      homPrecompose (middleRestrictionComparisonValue A B C D E F P Q b.unop e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D
    ((Bimodule.rightRestriction A C D E F Q).rightAt e)
    ((Bimodule.leftRestriction A B C D F P).leftAt b.unop)
  intro p g d k r i n ha hn q v
  exact middleRestrictionComparisonValue_rightAction A B C D E F P Q b b' d e
    (j := r + p) ha rfl hn g q v

lemma middleRestrictionComparisonValue_left_naturality (b : B) (e e' : E) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).leftAt b).map e e' ≫
      homPostcompose _ (middleRestrictionComparisonValue A B C D E F P Q b e') =
    ((compose A B C E P Q).leftAt b).map e e' ≫
      homPrecompose (middleRestrictionComparisonValue A B C D E F P Q b e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D
    ((Bimodule.rightRestriction A C D E F Q).rightAt e)
    ((Bimodule.leftRestriction A B C D F P).leftAt b)
  intro p g d k r i n ha hn q v
  exact middleRestrictionComparisonValue_leftAction A B C D E F P Q b d e e'
    (j := k + p) ha rfl hn g q v

end SerrePositivity.DifferentialGraded.BimoduleTensor

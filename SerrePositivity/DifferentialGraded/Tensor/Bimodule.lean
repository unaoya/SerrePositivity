module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleActions

/-! # 多対象dg bimoduleの相対tensor合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma paramTrans_unit (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) (b : Bᵒᵖ) :
    eId (Complex A) e ≫ (paramTrans A B C E P Q e e).app b =
      identity ((rightAt A B C E P Q e).obj b) := by
  change eId (Complex A) e ≫ (leftAt A B C E P Q b.unop).map e e =
    identity (BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b.unop))
  exact (leftAt A B C E P Q b.unop).map_id e

lemma paramTrans_comp (P : Bimodule A B C) (Q : Bimodule A C E)
    (e e' e'' : E) (b : Bᵒᵖ) :
    eComp (Complex A) e e' e'' ≫ (paramTrans A B C E P Q e e'').app b =
      ((paramTrans A B C E P Q e e').app b ⊗ₘ (paramTrans A B C E P Q e' e'').app b) ≫
        enrichedComposition _ _ _ :=
  (leftAt A B C E P Q b.unop).map_comp e e' e''

/-- Q(c,e)⊗_C P(b,c)を値とする、実際の右B・左E dg bimodule。 -/
def compose (P : Bimodule A B C) (Q : Bimodule A C E) : Bimodule A B E :=
  Bimodule.ofParamTrans A B E (rightAt A B C E P Q) (paramTrans A B C E P Q)
    (paramTrans_unit A B C E P Q) (paramTrans_comp A B C E P Q)

lemma compose_value (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    (compose A B C E P Q).value b e =
      BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) := rfl

lemma compose_rightMap (P : Bimodule A B C) (Q : Bimodule A C E)
    (e : E) (b b' : Bᵒᵖ) :
    ((compose A B C E P Q).rightAt e).map b b' =
      P.transposeHom b b' ≫ BalancedTensor.leftHomMap A C (Q.rightAt e)
        (P.leftAt b.unop) (P.leftAt b'.unop) := rfl

@[reassoc]
lemma compose_leftMap_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (e e' : E) (b : B) :
    (compose A B C E P Q).toFunctor.map e e' ≫
      moduleHomπ A B (rightAt A B C E P Q e) (rightAt A B C E P Q e') b =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b) :=
  Bimodule.ofParamTrans_map_π A B E (rightAt A B C E P Q) (paramTrans A B C E P Q)
    (paramTrans_unit A B C E P Q) (paramTrans_comp A B C E P Q) e e' b

end SerrePositivity.DifferentialGraded.BimoduleTensor

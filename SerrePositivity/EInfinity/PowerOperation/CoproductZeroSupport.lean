module

public import SerrePositivity.EInfinity.PowerOperation.CofanZeroSupport

/-!
# 零支持を除く、指定余積の同型

DAG XIII Construction 2.2.6 の有限対角線比較の補助。
［一般圏］基盤への移動候補。支持上の余積と全余積の同型を、
元の指定包含射とともに保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} (F : I → C) (P : I → Prop) [DecidablePred P]
variable (hzero : ∀ i, ¬ P i → IsZero (F i))
variable [HasCoproduct F] [HasCoproduct fun i : {i // P i} => F i.1]

/-- 同じ包含射を持つ、支持上の余積と全余積の指定同型。 -/
def coproductZeroSupportIso : (∐ fun i : {i // P i} => F i.1) ≅ ∐ F :=
  IsColimit.coconePointUniqueUpToIso
    (zeroExtendedCofanIsColimit F P hzero
      (Cofan.mk _ (Sigma.ι (fun i : {i // P i} => F i.1)))
      (colimit.isColimit _)) (colimit.isColimit _)

/-- 指定同型は、支持内の各指定包含射を保つ。 -/
@[reassoc]
lemma coproductZeroSupportIso_inclusion (i : {i // P i}) :
    Sigma.ι (fun i : {i // P i} => F i.1) i ≫ (coproductZeroSupportIso F P hzero).hom =
      Sigma.ι F i.1 := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (zeroExtendedCofanIsColimit F P hzero
      (Cofan.mk _ (Sigma.ι (fun i : {i // P i} => F i.1))) (colimit.isColimit _))
    (colimit.isColimit (Discrete.functor F)) (Discrete.mk i.1)
  change ((if hi : P i.1 then Sigma.ι (fun i : {i // P i} => F i.1) ⟨i.1, hi⟩
    else 0) : F i.1 ⟶ (∐ fun j : {j // P j} => F j.1)) ≫
      (coproductZeroSupportIso F P hzero).hom = Sigma.ι F i.1 at h
  rw [dite_eq_left i.2] at h
  exact h

end SerrePositivity.EInfinity.PowerOperation

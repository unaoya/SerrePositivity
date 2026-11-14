module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# 零の成分を加えた余積の錐

DAG XIII Construction 2.2.6 の上有界 orbit 模型の有限対角線比較の補助。
［一般圏］有限支持の余積の比較に使う、基盤への移動候補。
支持の外で零対象なら、支持上の余積の錐を零射で延長しても余極限である。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} (F : I → C) (P : I → Prop) [DecidablePred P]

/-- 支持上の余積の錐を、零射で全添字へ延長する。 -/
def zeroExtendedCofan (c : Cofan fun i : {i // P i} => F i.1) : Cofan F :=
  Cofan.mk c.pt fun i => if hi : P i then c.inj ⟨i, hi⟩ else 0

/-- 零成分の追加は、同じ指定射を保って余極限性を保つ。 -/
def zeroExtendedCofanIsColimit
    (hzero : ∀ i, ¬ P i → IsZero (F i))
    (c : Cofan fun i : {i // P i} => F i.1) (hc : IsColimit c) :
    IsColimit (zeroExtendedCofan F P c) := by
  refine Cofan.IsColimit.mk _
    (fun s => hc.desc (Cofan.mk s.pt fun i => s.inj i.1)) ?_ ?_
  · intro s i
    by_cases hi : P i
    · change (if h : P i then c.inj ⟨i, h⟩ else 0) ≫ _ = s.inj i
      rw [dite_eq_left hi]
      exact hc.fac (Cofan.mk s.pt fun j => s.inj j.1) (Discrete.mk ⟨i, hi⟩)
    · exact (hzero i hi).eq_of_src _ _
  · intro s m hm
    change c.pt ⟶ s.pt at m
    apply Cofan.IsColimit.hom_ext hc
    intro i
    have h := hm i.1
    change (if h : P i.1 then c.inj ⟨i.1, h⟩ else 0) ≫ m = s.inj i.1 at h
    rw [dite_eq_left i.2] at h
    exact h.trans (hc.fac (Cofan.mk s.pt fun j => s.inj j.1) (Discrete.mk i)).symm

end SerrePositivity.EInfinity.PowerOperation

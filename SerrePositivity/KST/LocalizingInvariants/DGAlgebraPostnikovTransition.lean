module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDesc

/-!
概要：有限 Postnikov 代数切断の遷移射と、厳密な恒等・合成・自然性を構成する。
方針：一意な代数降下を使い、全ての等式を元の商射へ前合成して証明する。
規約：遷移射は実代数射。使われ方：有限 Postnikov の塔と平方零比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]

def postnikovTransition (m n : ℤ) (h : n ≤ m) : postnikov R B m ⟶ postnikov R B n := by
  have : (postnikov R B n).X.IsStrictlyGE (-m) :=
    ((postnikovComplex R n).obj B).isStrictlyGE_of_ge (-m) (-n) (by omega)
  exact postnikovDesc R m (postnikovQuotient R B n)

lemma postnikovQuotient_transition (m n : ℤ) (h : n ≤ m) :
    postnikovQuotient R B m ≫ postnikovTransition R B m n h = postnikovQuotient R B n := by
  have : (postnikov R B n).X.IsStrictlyGE (-m) :=
    ((postnikovComplex R n).obj B).isStrictlyGE_of_ge (-m) (-n) (by omega)
  exact postnikovQuotient_desc R m _

lemma postnikovQuotient_cancel {C : Mon (Complex R)} (n : ℤ)
    {f g : postnikov R B n ⟶ C}
    (h : postnikovQuotient R B n ≫ f = postnikovQuotient R B n ≫ g) : f = g := by
  apply Mon.Hom.ext
  apply (cancel_epi (B.X.πTruncGE (-n))).1
  exact congrArg Mon.Hom.hom h

lemma postnikovTransition_id (n : ℤ) : postnikovTransition R B n n le_rfl = 𝟙 _ := by
  apply postnikovQuotient_cancel R B n
  rw [postnikovQuotient_transition, Category.comp_id]

lemma postnikovTransition_comp (l m n : ℤ) (hm : m ≤ l) (hn : n ≤ m) :
    postnikovTransition R B l m hm ≫ postnikovTransition R B m n hn =
      postnikovTransition R B l n (hn.trans hm) := by
  apply postnikovQuotient_cancel R B l
  rw [← Category.assoc, postnikovQuotient_transition, postnikovQuotient_transition,
    postnikovQuotient_transition]

lemma postnikovTransition_naturality {C : Mon (Complex R)} [C.X.IsStrictlyLE 0]
    (f : B ⟶ C) (m n : ℤ) (h : n ≤ m) :
    postnikovMap R f m ≫ postnikovTransition R C m n h =
      postnikovTransition R B m n h ≫ postnikovMap R f n := by
  apply postnikovQuotient_cancel R B m
  rw [← Category.assoc, postnikovQuotient_naturality, Category.assoc,
    postnikovQuotient_transition, ← Category.assoc, postnikovQuotient_transition,
    postnikovQuotient_naturality]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

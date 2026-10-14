module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 左随伴の比較を右随伴へ移す -/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.ActionComparisonAdjunction

open CategoryTheory

variable {C : Type u} [Category.{v} C] {L L' R R' : C ⥤ C}
  (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L')

/-- 左随伴の自然同型と右随伴の一意性から得る右随伴の自然同型。 -/
def rightIso : R ≅ R' := (a.ofNatIsoLeft e).rightAdjointUniq b

/-- 右随伴の比較が満たす、二つの評価の比較の法則。 -/
def evaluationLaw (X : C) : Prop :=
  L'.map ((rightIso a b e).hom.app X) ≫ b.counit.app X =
    e.inv.app (R.obj X) ≫ a.counit.app X

/-- 右随伴の比較は、左随伴の逆比較を介して元の評価を保つ。 -/
lemma rightIso_evaluation (X : C) : evaluationLaw a b e X :=
  (a.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit b X

/-- 左随伴の比較と右随伴の比較が、二つの転置を比較する法則。 -/
def homEquivLaw (X Y : C) (f : L'.obj X ⟶ Y) : Prop :=
  a.homEquiv X Y (e.hom.app X ≫ f) ≫ (rightIso a b e).hom.app Y = b.homEquiv X Y f

/-- 右随伴の比較を元の転置へ合成すると、比較後の左随伴の転置になる。 -/
lemma rightIso_homEquiv (X Y : C) (f : L'.obj X ⟶ Y) : homEquivLaw a b e X Y f := by
  change a.homEquiv X Y (e.hom.app X ≫ f) ≫ (rightIso a b e).hom.app Y = b.homEquiv X Y f
  rw [← Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [(rightIso a b e).hom.naturality f, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ R'.map f)
    ((a.ofNatIsoLeft e).unit_rightAdjointUniq_hom_app b X)

end SerrePositivity.ActionComparisonAdjunction

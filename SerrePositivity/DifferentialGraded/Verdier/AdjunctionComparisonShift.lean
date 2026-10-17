module
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 随伴の一意性による実際の比較同型の shift 整合性 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {M : Type*} [AddMonoid M] {C D : Type*} [Category* C] [Category* D]
  [HasShift C M] [HasShift D M]

/-- 同じ右随伴への二つの整合的随伴から得る既存の一意性同型は shift と可換する。 -/
lemma leftAdjointUniqCommShift {F F' : C ⥤ D} {R : D ⥤ C}
    [F.CommShift M] [F'.CommShift M] [R.CommShift M]
    (a : F ⊣ R) (b : F' ⊣ R) [a.CommShift M] [b.CommShift M] :
    NatTrans.CommShift (Adjunction.leftAdjointUniq a b).hom M := by
  let τ : F ⟶ F' :=
    F.leftUnitor.inv ≫ whiskerRight b.unit F ≫ (associator F' R F).hom ≫
      whiskerLeft F' a.counit ≫ F'.rightUnitor.hom
  have hτ : NatTrans.CommShift τ M := by
    dsimp [τ]
    infer_instance
  have he : (Adjunction.leftAdjointUniq a b).hom = τ := by
    apply NatTrans.ext
    funext X
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app a b X
    have h' := (a.homEquiv X (F'.obj X)).symm_apply_apply
      ((Adjunction.leftAdjointUniq a b).hom.app X)
    rw [h] at h'
    simp only [τ, NatTrans.comp_app, leftUnitor_inv_app, whiskerRight_app,
      associator_hom_app, whiskerLeft_app, rightUnitor_hom_app,
      Category.id_comp]
    rw [Adjunction.homEquiv_counit] at h'
    exact h'.symm.trans (congrArg (fun f => F.map (b.unit.app X) ≫ f)
      (Category.comp_id (a.counit.app (F'.obj X))).symm)
  rw [he]
  exact hτ

/-- 右関手の整合的自然同型による随伴の輸送は、既存の両 shift を保つ。 -/
lemma adjunctionOfNatIsoRightCommShift {F : C ⥤ D} {R R' : D ⥤ C}
    [F.CommShift M] [R.CommShift M] [R'.CommShift M]
    (a : F ⊣ R) [a.CommShift M] (e : R ≅ R') [NatTrans.CommShift e.hom M] :
    (a.ofNatIsoRight e).CommShift M := by
  apply Adjunction.CommShift.mk'
  change NatTrans.CommShift (a.unit ≫ whiskerLeft F e.hom) M
  infer_instance
end SerrePositivity.DifferentialGraded

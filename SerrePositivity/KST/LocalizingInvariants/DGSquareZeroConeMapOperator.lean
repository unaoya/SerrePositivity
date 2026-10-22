module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeOperator
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestriction

/-!
概要：包含の可換四角形は、平方零代数の追加微分の可換四角形を与える。
方針：元の二座標で作用素を評価し、shift 射と直和射の成分を計算する。
規約：元の底と層の実射を保持。使われ方：微分変更代数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B)
  (M : Bimod A A) (N : Bimod B B) (t : M ⟶ bimoduleRestrict q N)
  (i : M.X ⟶ A.X) (j : N.X ⟶ B.X) (hi : t.hom ≫ j = i ≫ q.hom)

def splitMap : splitAlgebra A M ⟶ splitAlgebra B N :=
  SquareZero.mapOver q (DGBimoduleShift.obj M 1) (DGBimoduleShift.obj N 1)
    (DGBimoduleShift.mapOver q N 1 t)

lemma splitMap_hom : (splitMap q M N t).hom = biprod.map q.hom (t.hom⟦(1 : ℤ)⟧') := by
  change biprod.map q.hom (DGBimoduleShift.mapOver q N 1 t).hom = _
  rw [DGBimoduleShift.mapOver_hom]
  rfl

include hi in
lemma operator_map : (operator A M i).comp (Cochain.ofHom (splitMap q M N t).hom) (add_zero 1) =
    (Cochain.ofHom (splitMap q M N t).hom).comp (operator B N j) (zero_add 1) := by
  apply Cochain.ext
  intro p r hpr
  obtain rfl : r = p + 1 := hpr.symm
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rw [operator_v, operator_v, splitMap_hom]
  let τ : (DGBimoduleShift.obj M 1).X ⟶ (DGBimoduleShift.obj N 1).X := t.hom⟦(1 : ℤ)⟧'
  change ((biprod.snd : A.X ⊞ (DGBimoduleShift.obj M 1).X ⟶ _).f p ≫
    i.f (p + 1) ≫ (biprod.inl : A.X ⟶ A.X ⊞ (DGBimoduleShift.obj M 1).X).f (p + 1)) ≫
      (biprod.map q.hom τ).f (p + 1) = (biprod.map q.hom τ).f p ≫
        (biprod.snd : B.X ⊞ (DGBimoduleShift.obj N 1).X ⟶ _).f p ≫ j.f (p + 1) ≫
          (biprod.inl : B.X ⟶ B.X ⊞ (DGBimoduleShift.obj N 1).X).f (p + 1)
  have h₁ := congrArg (fun f => f.f (p + 1)) (biprod.inl_map q.hom τ)
  have h₂ := congrArg (fun f => f.f p) (biprod.map_snd q.hom τ)
  have ht : τ.f p = t.hom.f (p + 1) := rfl
  have he := congrArg (fun f => f.f (p + 1)) hi
  simp only [HomologicalComplex.comp_f] at h₁ h₂ he
  rw [Category.assoc, Category.assoc, h₁]
  rw [← Category.assoc ((biprod.map q.hom τ).f p), h₂]
  simpa only [Category.assoc, ht] using (congrArg (fun z =>
    (biprod.snd : A.X ⊞ (DGBimoduleShift.obj M 1).X ⟶ _).f p ≫ z ≫
      (biprod.inl : B.X ⟶ B.X ⊞ (DGBimoduleShift.obj N 1).X).f (p + 1)) he).symm

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

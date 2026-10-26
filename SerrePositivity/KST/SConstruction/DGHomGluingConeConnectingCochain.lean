module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeCochain
public import SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit
public import SerrePositivity.DifferentialGraded.Complexes.Shift

/-!
概要：元三成分 cone 作用は connecting 射と全次数で自然に可換となる。
方針：元の fst 回収式と target shift の同じ Koszul 符号を照合する。
規約：第三 cochain を省略しない。使われ方：LT 逆回転の実 dg 関手の全 Hom 自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
private lemma connectingSign {V : Type*} [Category V] [Preadditive V] [Linear ℤ V]
    {X Y Z W : V} (k : X ⟶ Y) (t : Y ⟶ W) (s : X ⟶ Z) (a : Z ⟶ W) (r : ℤˣ)
    (he : k ≫ t = r • (s ≫ a)) : k ≫ (-t) = (-s) ≫ (r • a) := by
  obtain rfl | rfl := Int.units_eq_one_or r
  · simpa only [Units.smul_def, Units.val_one, one_smul, Preadditive.comp_neg,
      Preadditive.neg_comp] using congrArg Neg.neg he
  · simpa only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] using congrArg Neg.neg he

variable {R : Type u} [CommRing R] {A B C D : Complex R}

/-- 概要：同じ実 cone の connecting 射は元の全三成分作用について自然。
方針：左 shift の元符号を同じ target shift の符号へ照合する。
規約：全斉次射と元第三比較を保持。使われ方：逆回転の閉射族を dg 自然変換へ束ねる。 -/
lemma dgGluingConeCochain_connecting (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m) (hm : m + 1 = n) :
    (dgGluingConeCochain f g a b h hm).comp
        (Cochain.ofHom (mappingCone.triangle g).mor₃) (add_zero n) =
      (Cochain.ofHom (mappingCone.triangle f).mor₃).comp
        ((shiftHom 1 A C).f n a) (zero_add n) := by
  apply Cochain.ext
  intro i j hij
  apply (Cochain.comp_zero_cochain_v (dgGluingConeCochain f g a b h hm)
    (Cochain.ofHom (mappingCone.triangle g).mor₃) i j hij).trans
  apply (congrArg (fun c => (dgGluingConeCochain f g a b h hm).v i j hij ≫ c)
    (Cochain.ofHom_v (mappingCone.triangle g).mor₃ j)).trans
  apply Eq.trans _ (Cochain.zero_cochain_comp_v
    (Cochain.ofHom (mappingCone.triangle f).mor₃) ((shiftHom 1 A C).f n a) i j hij).symm
  apply Eq.trans _ (congrArg (fun c => c ≫ ((shiftHom 1 A C).f n a).v i j hij)
    (Cochain.ofHom_v (mappingCone.triangle f).mor₃ i)).symm
  rw [complexConeGradedProjection_eq_connecting, complexConeGradedProjection,
    complexConeGradedProjection_eq_connecting, complexConeGradedProjection, shiftHom_v]
  change (dgGluingConeCochain f g a b h hm).v i j hij ≫
      (-(mappingCone.fst g).val.v j (j + 1) rfl) =
    (-(mappingCone.fst f).val.v i (i + 1) rfl) ≫
      ((1 * n).negOnePow • a.v (i + 1) (j + 1) (by omega))
  have he := Cochain.congr_v (dgGluingConeCochain_fst f g a b h hm) i (j + 1) (by omega)
  rw [Cochain.comp_v _ _ rfl i j (j + 1) hij rfl,
    Cochain.units_smul_v, Cochain.comp_v _ _ (by omega : 1 + n = n + 1)
      i (i + 1) (j + 1) rfl (by omega)] at he
  exact connectingSign _ _ _ _ (1 * n).negOnePow
    (by simpa only [one_mul] using he)
end SerrePositivity.KST.SConstruction

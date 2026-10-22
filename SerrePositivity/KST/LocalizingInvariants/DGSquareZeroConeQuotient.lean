module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbationMapTo
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeComplexIso
public import SerrePositivity.KST.LocalizingInvariants.CochainConeQuotientComparison

/-!
概要：層包含を零化する底への代数射から、微分変更後の実代数射を作る。
方針：作用素の正包含成分を零化し、元の cone の商比較へ二座標を保って同定する。
規約：元の商射を保持する。使われ方：Postnikov の実全射準同型分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  (f : M ⟶ Bimod.regular A) (k : ℤ) (hk : k < 0)
  [M.X.IsStrictlyGE k] [M.X.IsStrictlyLE k]
  {B : Mon (Complex R)} (q : A ⟶ B) (hi : f.hom ≫ q.hom = 0)

include hi in
lemma operator_quotient_zero : (operator A M f.hom).comp
    (Cochain.ofHom (SquareZero.projection A (DGBimoduleShift.obj M 1) ≫ q).hom)
      (add_zero 1) = 0 := by
  apply Cochain.ext
  intro p r hpr
  obtain rfl : r = p + 1 := hpr.symm
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v]
  change (operator A M f.hom).v p (p + 1) rfl ≫
    (baseF A M f.hom (p + 1) ≫ q.hom.f (p + 1)) = 0
  rw [← Category.assoc, operator_baseF, Category.assoc]
  have he : f.hom.f (p + 1) ≫ q.hom.f (p + 1) = 0 := congrArg (fun t => t.f (p + 1)) hi
  rw [he, comp_zero]

def quotient : algebra A M f k hk ⟶ B :=
  AlgebraPerturbation.mapTo (splitAlgebra A M) (operator A M f.hom)
    (operator_closed A M f.hom) (operator_square_zero A M f.hom)
    (operator_isDerivation A M f k hk) (operator_unit A M f.hom)
    (SquareZero.projection A (DGBimoduleShift.obj M 1) ≫ q) (operator_quotient_zero A M f q hi)

lemma quotient_f (p : ℤ) : (quotient A M f k hk q hi).hom.f p =
    baseF A M f.hom p ≫ q.hom.f p := rfl

lemma quotient_hom_eq : (quotient A M f k hk q hi).hom =
    (complexIso A M f.hom).hom ≫ cochainConeQuotient f.hom q.hom hi := by
  apply HomologicalComplex.hom_ext
  intro p
  change baseF A M f.hom p ≫ q.hom.f p = gradedToCone A M f.hom p ≫
    (cochainConeQuotient f.hom q.hom hi).f p
  have hc : (cochainConeQuotient f.hom q.hom hi).f p =
      (mappingCone.snd f.hom).v p p (add_zero p) ≫ q.hom.f p := by
    rw [cochainConeQuotient, mappingCone.desc_f _ _ _ _ p (p + 1) rfl,
      Cochain.zero_v, comp_zero, zero_add]
  rw [hc, ← Category.assoc, gradedToCone_snd]

lemma quotient_epi [Epi q.hom] : Epi (quotient A M f k hk q hi).hom := by
  rw [quotient_hom_eq]
  have := cochainConeQuotient_epi f.hom q.hom hi
  infer_instance

lemma quotient_quasiIso [Epi q.hom] (hrep : QuasiIso (kernel.lift q.hom f.hom hi)) :
    QuasiIso (quotient A M f k hk q hi).hom := by
  rw [quotient_hom_eq]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _)
    (hφ' := cochainConeQuotient_quasiIso f.hom q.hom hi hrep)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

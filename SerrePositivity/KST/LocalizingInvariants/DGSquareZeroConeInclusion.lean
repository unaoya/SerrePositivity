module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbationMapFrom
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeClassMap
public import SerrePositivity.KST.LocalizingInvariants.CochainConeShortExact

/-!
概要：元の上段代数を摂動代数へ実代数射で包含し、元の cone 包含と両脚を保つ。
方針：追加作用素が消す零切断を移送し、二座標で等式を検証する。
規約：包含は underlying 複体でも単射。使われ方：Postnikov の実代数 pullback。
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

def inclusion : A ⟶ algebra A M f k hk :=
  AlgebraPerturbation.mapFrom (splitAlgebra A M) (operator A M f.hom)
    (operator_closed A M f.hom) (operator_square_zero A M f.hom)
    (operator_isDerivation A M f k hk) (operator_unit A M f.hom)
    (SquareZero.zeroSection A (DGBimoduleShift.obj M 1)) (operator_inl A M f.hom)

lemma inclusion_f (p : ℤ) : (inclusion A M f k hk).hom.f p =
    baseInclusionF A M f.hom p := rfl

lemma inclusion_toCone : (inclusion A M f k hk).hom ≫ (complexIso A M f.hom).hom =
    mappingCone.inr f.hom := by
  apply HomologicalComplex.hom_ext
  intro p
  change baseInclusionF A M f.hom p ≫ gradedToCone A M f.hom p = (mappingCone.inr f.hom).f p
  apply mappingCone.ext_to f.hom p (p + 1) rfl
  · rw [Category.assoc, gradedToCone_fst, baseInclusionF_coefficientF,
      mappingCone.inr_f_fst_v]
  · rw [Category.assoc, gradedToCone_snd, baseInclusionF_baseF, mappingCone.inr_f_snd_v]
    rfl

lemma inclusion_mono : Mono (inclusion A M f k hk).hom := by
  have := cochainConeInr_mono f.hom
  exact mono_of_mono_fac (inclusion_toCone A M f k hk)

variable {B : Mon (Complex R)} (q : A ⟶ B) (hi : f.hom ≫ q.hom = 0)

lemma inclusion_quotient : inclusion A M f k hk ≫ quotient A M f k hk q hi = q := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  change baseInclusionF A M f.hom p ≫ (baseF A M f.hom p ≫ q.hom.f p) = q.hom.f p
  rw [← Category.assoc, baseInclusionF_baseF, Category.id_comp]

lemma inclusion_class (N : Bimod B B)
    (c : DGBimoduleShift.obj M 1 ⟶ bimoduleRestrict q N) :
    inclusion A M f k hk ≫ classMap A M f k hk q N c hi = q ≫ SquareZero.zeroSection B N := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  exact congrArg (fun t => t.f p)
    (biprod.inl_map q.hom (c.hom : (DGBimoduleShift.obj M 1).X ⟶ N.X))

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

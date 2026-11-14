module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeMapProjections

/-!
概要：mapping cocone の二座標を、元の cone の次数をずらした二座標で計算する。
方針：実 shift 定義とその定数符号を簡約する。
規約：両座標とも元の符号を保持。使われ方：cocone 射の準同型性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (d : K ⟶ L)

lemma cochainCocone_fst_f (p : ℤ) : (mappingCocone.fst d).f p =
    (mappingCone.fst d).val.v (p - 1) p (by omega) := by
  simp [mappingCocone.fst, Cocycle.homOf, Cocycle.leftShift, Cochain.leftShift,
    CochainComplex.shiftFunctorObjXIso, sub_eq_add_neg,
    show (2 : ℤ).negOnePow = 1 from rfl]
  rfl

lemma cochainCocone_snd_v (p : ℤ) : (mappingCocone.snd d).v p (p - 1) (by omega) =
    (mappingCone.snd d).v (p - 1) (p - 1) (add_zero (p - 1)) := by
  simp [mappingCocone.snd, Cochain.leftShift, CochainComplex.shiftFunctorObjXIso, sub_eq_add_neg,
    show (2 : ℤ).negOnePow = 1 from rfl]
  rfl

end SerrePositivity.KST.LocalizingInvariants

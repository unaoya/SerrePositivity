module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftLaws

/-!
概要：任意整数 shift を、実 dg 双加群の関手として構成する。
方針：符号付き作用の検証済み三則を使い、射は元の chain map の shift を使う。
規約：恒等・合成は厳密に保持。使われ方：Postnikov 拡大の shift 係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A : Mon (Complex R)}

def obj (M : Bimod A A) (s : ℤ) : Bimod A A where
  X := M.X⟦s⟧
  actLeft := actLeft M s
  actRight := actRight M s
  one_actLeft := one_actLeft M s
  actRight_one := actRight_one M s
  left_assoc := left_assoc M s
  right_assoc := right_assoc M s
  middle_assoc := middle_assoc M s

def map {M N : Bimod A A} (f : M ⟶ N) (s : ℤ) : obj M s ⟶ obj N s where
  hom := f.hom⟦s⟧'
  left_act_hom := actLeft_naturality M s f
  right_act_hom := actRight_naturality M s f

def functor (A : Mon (Complex R)) (s : ℤ) : Bimod A A ⥤ Bimod A A where
  obj M := obj M s
  map f := map f s
  map_id M := by
    apply Bimod.Hom.ext
    exact (shiftFunctor (Complex R) s).map_id M.X
  map_comp f g := by
    apply Bimod.Hom.ext
    exact (shiftFunctor (Complex R) s).map_comp f.hom g.hom

lemma obj_upperBound (M : Bimod A A) (s k : ℤ) [M.X.IsStrictlyLE k] :
    (obj M s).X.IsStrictlyLE (k - s) :=
  CochainComplex.isStrictlyLE_shift _ k s (k - s) (by omega)

lemma obj_lowerBound (M : Bimod A A) (s k : ℤ) [M.X.IsStrictlyGE k] :
    (obj M s).X.IsStrictlyGE (k - s) :=
  CochainComplex.isStrictlyGE_shift _ k s (k - s) (by omega)

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift

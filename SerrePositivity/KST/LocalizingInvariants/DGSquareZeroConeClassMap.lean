module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeQuotient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver

/-!
概要：底への零化を保つ実平方零 class を、微分変更後の実代数射として構成する。
方針：元の底変更・係数射が追加作用素を消すことを二座標で示す。
規約：係数の符号を自由に選べる。使われ方：標準 cone 境界と同じ負符号の class。
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
  {B : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (c : DGBimoduleShift.obj M 1 ⟶ bimoduleRestrict q N) (hi : f.hom ≫ q.hom = 0)

include hi in
lemma operator_class_zero : (operator A M f.hom).comp
    (Cochain.ofHom (SquareZero.mapOver q (DGBimoduleShift.obj M 1) N c).hom) (add_zero 1) = 0 := by
  apply Cochain.ext
  intro p r hpr
  obtain rfl : r = p + 1 := hpr.symm
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v]
  have hv : (operator A M f.hom).v p (p + 1) rfl =
      coefficientF A M f.hom p ≫ f.hom.f (p + 1) ≫ baseInclusionF A M f.hom (p + 1) :=
    operator_v A M f.hom p
  have hm : baseInclusionF A M f.hom (p + 1) ≫
      (SquareZero.mapOver q (DGBimoduleShift.obj M 1) N c).hom.f (p + 1) =
      q.hom.f (p + 1) ≫ (biprod.inl : B.X ⟶ (SquareZero.algebra B N).X).f (p + 1) :=
    congrArg (fun t => t.f (p + 1))
      (biprod.inl_map q.hom (c.hom : (DGBimoduleShift.obj M 1).X ⟶ N.X))
  rw [hv, Category.assoc, Category.assoc, hm, ← Category.assoc, ← Category.assoc]
  have he : f.hom.f (p + 1) ≫ q.hom.f (p + 1) = 0 := congrArg (fun t => t.f (p + 1)) hi
  rw [Category.assoc (coefficientF A M f.hom p), he, comp_zero, zero_comp]

def classMap : algebra A M f k hk ⟶ SquareZero.algebra B N :=
  AlgebraPerturbation.mapTo (splitAlgebra A M) (operator A M f.hom)
    (operator_closed A M f.hom) (operator_square_zero A M f.hom)
    (operator_isDerivation A M f k hk) (operator_unit A M f.hom)
    (SquareZero.mapOver q (DGBimoduleShift.obj M 1) N c) (operator_class_zero A M f q N c hi)

lemma classMap_f (p : ℤ) : (classMap A M f k hk q N c hi).hom.f p =
    (biprod.map q.hom (c.hom : (DGBimoduleShift.obj M 1).X ⟶ N.X)).f p := rfl

lemma classMap_projection : classMap A M f k hk q N c hi ≫ SquareZero.projection B N =
    quotient A M f k hk q hi := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  exact congrArg (fun t => t.f p)
    (biprod.map_fst q.hom (c.hom : (DGBimoduleShift.obj M 1).X ⟶ N.X))

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

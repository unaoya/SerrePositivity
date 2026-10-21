module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
概要：厳密な非正次数 dg 代数上の有限 Postnikov 関手と自然な商射を供給する。
方針：切断の元の chain map を使い、connective cover も同じ源へ持ち上げる。
規約：厳密な関手則を検証する。使われ方：実 dg 代数の塔の切断。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def nonpositiveProperty : ObjectProperty (Mon (Complex R)) := fun B ↦ B.X.IsStrictlyLE 0

abbrev NonpositiveAlgebra := (nonpositiveProperty R).FullSubcategory

instance nonpositiveAlgebra_nonpositive (B : NonpositiveAlgebra R) :
    B.obj.X.IsStrictlyLE 0 := B.property

def nonpositiveInclusion : NonpositiveAlgebra R ⥤ Mon (Complex R) :=
  (nonpositiveProperty R).ι

def postnikovFunctor (n : ℤ) : NonpositiveAlgebra R ⥤ Mon (Complex R) where
  obj B := postnikov R B.obj n
  map f := postnikovMap R f.hom n
  map_id B := by
    apply Mon.Hom.ext
    exact (postnikovComplex R n).map_id B.obj
  map_comp f g := by
    apply Mon.Hom.ext
    exact (postnikovComplex R n).map_comp f.hom g.hom

def postnikovQuotientNatTrans (n : ℤ) : nonpositiveInclusion R ⟶ postnikovFunctor R n where
  app B := postnikovQuotient R B.obj n
  naturality {_ _} f := (postnikovQuotient_naturality R f.hom n).symm

lemma postnikovFunctor_underlying (n : ℤ) :
    postnikovFunctor R n ⋙ Mon.forget (Complex R) =
      nonpositiveInclusion R ⋙ postnikovComplex R n := rfl

def connectiveCoverNonpositive : Mon (Complex R) ⥤ NonpositiveAlgebra R where
  obj B := ⟨connectiveCover R B, coverComplex_nonpositive R B⟩
  map f := ObjectProperty.homMk (connectiveCoverMap R f)
  map_id B := by
    apply ObjectProperty.hom_ext
    exact (connectiveCoverFunctor R).map_id B
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (connectiveCoverFunctor R).map_comp f g

lemma connectiveCoverNonpositive_inclusion :
    connectiveCoverNonpositive R ⋙ nonpositiveInclusion R = connectiveCoverFunctor R := rfl

/-- 任意の dg 代数を、実非正次数 cover を経由して有限切断する厳密な関手。 -/
def coveredPostnikovFunctor (n : ℤ) : Mon (Complex R) ⥤ Mon (Complex R) :=
  connectiveCoverNonpositive R ⋙ postnikovFunctor R n

def coveredPostnikovQuotient (n : ℤ) :
    connectiveCoverFunctor R ⟶ coveredPostnikovFunctor R n :=
  Functor.whiskerLeft (connectiveCoverNonpositive R) (postnikovQuotientNatTrans R n)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

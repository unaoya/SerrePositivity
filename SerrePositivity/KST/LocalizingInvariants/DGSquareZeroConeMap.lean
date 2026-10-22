module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbationMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeMapOperator
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeDerivation

/-!
概要：実層包含の可換四角形から、微分変更した非可換平方零代数の射を構成する。
方針：追加微分の可換性を、元の分裂代数射の両側微分変更へ渡す。
規約：負次数に集中した二つの層。使われ方：Postnikov 拡大の実自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroCone
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B)
  (M : Bimod A A) (N : Bimod B B) (t : M ⟶ bimoduleRestrict q N)
  (i : M ⟶ Bimod.regular A) (j : N ⟶ Bimod.regular B)
  (hi : t.hom ≫ j.hom = i.hom ≫ q.hom) (k : ℤ) (hk : k < 0)
  [M.X.IsStrictlyGE k] [M.X.IsStrictlyLE k] [N.X.IsStrictlyGE k] [N.X.IsStrictlyLE k]

def map : algebra A M i k hk ⟶ algebra B N j k hk :=
  AlgebraPerturbation.map (splitAlgebra A M) (splitAlgebra B N)
    (operator A M i.hom) (operator B N j.hom)
    (operator_closed A M i.hom) (operator_square_zero A M i.hom)
    (operator_closed B N j.hom) (operator_square_zero B N j.hom)
    (operator_isDerivation A M i k hk) (operator_unit A M i.hom)
    (operator_isDerivation B N j k hk) (operator_unit B N j.hom)
    (splitMap q M N t) (operator_map q M N t i.hom j.hom hi)

lemma map_f (p : ℤ) : (map q M N t i j hi k hk).hom.f p =
    (Limits.biprod.map q.hom (t.hom⟦(1 : ℤ)⟧')).f p :=
  congrArg (fun f => f.f p) (splitMap_hom q M N t)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroCone

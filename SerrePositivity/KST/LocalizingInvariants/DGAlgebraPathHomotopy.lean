module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathDiagonal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathEndpoints
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology

/-!
概要：実経路代数に値を持つ代数射から、元の両端射の鎖ホモトピーを回収する。
方針：実端点ホモトピーを前合成し、元の dg 代数の H⁻ʲ 関手へ送る。
規約：任意の鎖ホモトピーを乗法的とは扱わない。使われ方：導来代数写像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)}

structure Witness (f g : A ⟶ B) where
  hom : A ⟶ algebra R B
  source_eq : hom ≫ source R B = f
  target_eq : hom ≫ target R B = g

variable {R}

def Witness.chainHomotopy {f g : A ⟶ B} (h : Witness R f g) : Homotopy f.hom g.hom := by
  have a : h.hom.hom ≫ (source R B).hom = f.hom := congrArg Mon.Hom.hom h.source_eq
  have b : h.hom.hom ≫ (target R B).hom = g.hom := congrArg Mon.Hom.hom h.target_eq
  have t := (endpointsHomotopy R B).compLeft h.hom.hom
  rw [a, b] at t
  exact t

def Witness.refl (f : A ⟶ B) : Witness R f f where
  hom := f ≫ diagonal R B
  source_eq := by rw [Category.assoc, diagonal_source, Category.comp_id]
  target_eq := by rw [Category.assoc, diagonal_target, Category.comp_id]

def Witness.precomp {D : Mon (Complex R)} {f g : A ⟶ B} (h : Witness R f g) (a : D ⟶ A) :
    Witness R (a ≫ f) (a ≫ g) where
  hom := a ≫ h.hom
  source_eq := by rw [Category.assoc, h.source_eq]
  target_eq := by rw [Category.assoc, h.target_eq]

lemma Witness.groups_eq {f g : A ⟶ B} (h : Witness R f g) (j : ℤ) :
    (groups R j).map f = (groups R j).map g := by
  change AddCommGrpCat.toCommGrp.map ((forget₂ (ModuleCat R) AddCommGrpCat).map
    (homologyMap f.hom (-j))) =
      AddCommGrpCat.toCommGrp.map ((forget₂ (ModuleCat R) AddCommGrpCat).map
        (homologyMap g.hom (-j)))
  rw [h.chainHomotopy.homologyMap_eq]

lemma isConnective (hB : IsConnective R B) : IsConnective R (algebra R B) := by
  have := source_quasiIso R B
  have : B.X.IsLE 0 := hB
  apply (CochainComplex.isLE_iff _ 0).2
  intro i hi
  exact (exactAt_iff_of_quasiIsoAt (source R B).hom i).2
    (CochainComplex.exactAt_of_isLE B.X 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path

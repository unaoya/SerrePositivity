module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
概要：元の shift 層のホモロジーを、元の代数の下端ホモロジーへ自然に同定する。
方針：shift とホモロジーの元の自然同型を、既存の層包含と商の比較へ合成する。
規約：任意整数 shift と元の層射を保持。使われ方：像係数の元のホモロジー像との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

def postnikovShiftedLayerHomologyIso :
    (postnikovShiftedLayerBimodule R B n hn s).X.homology (-(n + 1) - s) ≅
      B.X.homology (-(n + 1)) :=
  (((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso s (-(n + 1) - s) (-(n + 1))
    (by omega)).app (postnikovLayer R B n)) ≪≫ postnikovLayerHomologyIso R B n

lemma postnikovShiftedLayerHomologyIso_naturality {C : Mon (Complex R)} [C.X.IsStrictlyLE 0]
    (f : B ⟶ C) : homologyMap (postnikovShiftedLayerMap R B n hn s f).hom (-(n + 1) - s) ≫
      (postnikovShiftedLayerHomologyIso R C n hn s).hom =
        (postnikovShiftedLayerHomologyIso R B n hn s).hom ≫ homologyMap f.hom (-(n + 1)) := by
  let e := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso s
    (-(n + 1) - s) (-(n + 1)) (by omega)
  have he : homologyMap ((postnikovLayerMap R f n)⟦s⟧') (-(n + 1) - s) ≫
      (e.app (postnikovLayer R C n)).hom = (e.app (postnikovLayer R B n)).hom ≫
        homologyMap (postnikovLayerMap R f n) (-(n + 1)) := e.hom.naturality _
  have hm := congrArg (fun t => homologyMap t (-(n + 1) - s))
    (postnikovShiftedLayerMap_hom R B n hn s f)
  rw [hm]
  change homologyMap ((postnikovLayerMap R f n)⟦s⟧') (-(n + 1) - s) ≫
      (e.app (postnikovLayer R C n)).hom ≫ (postnikovLayerHomologyIso R C n).hom =
        ((e.app (postnikovLayer R B n)).hom ≫ (postnikovLayerHomologyIso R B n).hom) ≫ _
  rw [← Category.assoc, he, Category.assoc, postnikovLayerHomologyIso_naturality]
  rw [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

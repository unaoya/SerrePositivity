module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology

/-!
概要：元の整数次数群の零射から、元のホモロジー加群射の零性を回収する。
方針：乗法表示の元を元の加法表示へ戻し、同じ線形写像の各値を比較する。
規約：元の代数射を保持。使われ方：pro 群の零遷移を実 Postnikov 像拡大へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (f : B ⟶ C) (j : ℤ)

lemma homologyMap_eq_zero_of_groups_zero (h : (groups R j).map f = 0) :
    homologyMap f.hom (-j) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun k => k.hom (Multiplicative.ofAdd x)) h
  rw [ProGroup.zero_apply] at hx
  change Multiplicative.ofAdd ((homologyMap f.hom (-j)).hom x) = Multiplicative.ofAdd 0 at hx
  exact congrArg Multiplicative.toAdd hx

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

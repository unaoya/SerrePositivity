module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofLeftPathStrictification
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveInverseRoofStrictSource

/-!
概要：実右三角形と、全射準同型細分上の実左経路から非正次数の両逆 roof を構成する。
方針：mapping-path で左経路を厳密化し、二重 cell と cover で元の両脚を保持する。
規約：左経路の実証人を要求する。使われ方：二切断対角反映の完成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : NativeRightInverseRoof R f i m hi)
  [(X.obj m).X.IsStrictlyLE 0] [(Y.obj m).X.IsStrictlyLE 0]
  {T : Mon (Complex R)} (e : T ⟶ X.obj m)
  (he : ∀ n : ℤ, Function.Surjective (e.hom.f n)) (hq : QuasiIso e.hom)
  (a : T ⟶ c.roof.apex) (ha : a ≫ c.roof.denominator = e ≫ f.app m)
  (w : Path.Witness R (a ≫ c.roof.numerator) (e ≫ X.transition hi))

def NativeRightInverseRoof.nonpositiveOfLeftPath : NonpositiveInverseRoof R f i m hi := by
  let r := c.roof.leftPathReplacement R
  let r' := r.cellRefinement R 2
  let v := c.roof.leftPathReplacementLift R a (e ≫ X.transition hi) w
  let l := r.cellRefinementLift R 2 v
  let p := cellAugmentation R T ≫ e
  let c' : NativeRightInverseRoof R f i m hi :=
    ⟨r', c.roof.leftPathReplacementRightPath R (f.app i) (Y.transition hi) c.rightPath⟩
  have hp : ∀ n : ℤ, Function.Surjective (p.hom.f n) := by
    intro n
    exact (he n).comp (cellAugmentation_surjective R T n)
  have hq' : QuasiIso p.hom := quasiIso_comp _ _
    (hφ := cellAugmentation_quasiIso R T) (hφ' := hq)
  have hd : l ≫ r'.denominator = p ≫ f.app m := by
    have hl := r.cellRefinementLift_denominator R 2 v
    have hv := c.roof.leftPathReplacementLift_denominator R a (e ≫ X.transition hi) w
    exact hl.trans ((congrArg (fun t => cellAugmentation R T ≫ t) hv).trans
      ((congrArg (fun t => cellAugmentation R T ≫ t) ha).trans (Category.assoc _ _ _).symm))
  have hn : l ≫ r'.numerator = p ≫ X.transition hi := by
    have hl := r.cellRefinementLift_numerator R 2 v
    have hv := c.roof.leftPathReplacementLift_numerator R a (e ≫ X.transition hi) w
    exact hl.trans ((congrArg (fun t => cellAugmentation R T ≫ t) hv).trans
      (Category.assoc _ _ _).symm)
  exact c'.nonpositiveOfStrictSource R p hp hq' l hd hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

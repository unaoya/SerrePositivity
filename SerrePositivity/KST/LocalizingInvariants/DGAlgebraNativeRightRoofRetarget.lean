module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightInverseRoof

/-!
概要：実右逆 roof の標的段を元の遷移で下げ、元の右経路を保持する。
方針：分子へ元の遷移を後合成し、同じ経路の標的遷移と自然性を使う。
規約：分母と頂点を取り替えない。使われ方：対角反映の後の右三角形。
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
  {f : LevelHom X Y} {i m k : ℕ} {hmk : m ≤ k}
  (c : NativeRightInverseRoof R f m k hmk) (him : i ≤ m)

def NativeRightInverseRoof.retarget : NativeRightInverseRoof R f i k (him.trans hmk) := by
  let w := c.rightPath.postcomp (Y.transition him)
  refine ⟨c.roof.postcompose R (X.transition him),
    ⟨w.hom, w.source_eq.trans ?_, w.target_eq.trans ?_⟩⟩
  · change (c.roof.numerator ≫ f.app m) ≫ Y.transition him =
      (c.roof.numerator ≫ X.transition him) ≫ f.app i
    rw [Category.assoc, ← f.naturality him, ← Category.assoc]
  · change (c.roof.denominator ≫ Y.transition hmk) ≫ Y.transition him =
      c.roof.denominator ≫ Y.transition (him.trans hmk)
    rw [Category.assoc, ← Y.transition_comp hmk him]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

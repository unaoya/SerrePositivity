module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# 射影対象の直和因子である cokernel

概要：射影対象への分裂単射の cokernel は射影。
方針：実 cokernel の標準分裂から retract を作る。
規約：単射の始域に射影性を要求しない。
使われ方：正規化境界の各次数の射影 cokernel。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Preadditive C]

lemma splitMono_cokernel_projective {X Y : C} (i : X ⟶ Y)
    [IsSplitMono i] [HasCokernel i] [Projective Y] : Projective (cokernel i) := by
  let b := binaryBiconeOfIsSplitMonoOfCokernel (cokernelIsCokernel i)
  let r : Retract (cokernel i) Y := { i := b.inr, r := b.snd, retract := b.inr_snd }
  exact r.projective

end SerrePositivity.ComplexLimits

module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCochainLift
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoefficientCycles
/-!
概要：元の Hom 係数を含むκコードで、任意シフト自由 sphere 間の閉射を持ち上げる。
方針：閉斉次係数をコードへ持ち上げ、同じ次数の cycle から自由 sphere 閉射を逆構成する。
規約：係数の評価後の厳密一致を証明し、実延長の端点同型との比較は別工程とする。
使われ方：c′ の全シフト自由行列の各係数の共通源持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)
  (n m : ℤ)
  (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
  (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
    linearSpan source target degree R D value coefficient x y (n - m))

def codeFreeSphereClosedArrow :
    freeSphere R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x n ⟶
      freeSphere R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) y m :=
  freeSphereClosedCoefficientPreimage R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y n m
    ⟨codeCochainLift R D κ a source target degree value coefficient hκ hI x y (n - m)
      (freeSphereClosedCoefficient R D (value x) (value y) n m f) hf,
      codeCochainLift_differential R D κ a source target degree value coefficient hκ hI x y (n - m)
        (freeSphereClosedCoefficient R D (value x) (value y) n m f) hf
        (freeSphereClosedCoefficient_closed R D (value x) (value y) n m f)⟩

lemma codeFreeSphereClosedArrow_coefficient_map :
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f (n - m)
      (freeSphereClosedCoefficient R
        ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y n m
        (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)) =
      freeSphereClosedCoefficient R D (value x) (value y) n m f := by
  rw [codeFreeSphereClosedArrow, freeSphereClosedCoefficientPreimage_coefficient]
  exact codeCochainLift_map R D κ a source target degree value coefficient hκ hI x y (n - m) _ hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded

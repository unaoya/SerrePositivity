module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageTransport

/-! # 元の最高生成元微分の指定次数への移送
概要：元の最高生成元の全面微分を、元の HA 指定次数とその次の次数で回収する。
方針：元の複体の微分と次数移送を交換し、同じ線形射で元の全面和を送る。
規約：元の面射・向き・全有限和を保持。使われ方：native HA 全高次方程式の微分側。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
open scoped BigOperators
variable (A : Type u) [CommRing A]

/-- 元の複体の微分は、始域・終域の元の次数移送と可換。 -/
lemma complexDifferential_degree_transport (K : Complex A) {p q r s : ℤ}
    (hp : p = r) (hq : q = s) (w : K.X p) :
    K.d r s (eqToHom (congrArg K.X hp) w) =
      eqToHom (congrArg K.X hq) (K.d p q w) := by
  cases hp
  cases hq
  rfl

/-- 元の最高生成元像の微分を指定次数へ移すと、元の全面像の同じ符号付き和になる。 -/
lemma serreCubeTopCellImage_cast_d (K : Complex A) (n : ℕ) (k : ℤ)
    (hk : -((n + 1 : ℕ) : ℤ) = k) (ht : -(n : ℤ) = k + 1)
    (f : serreCubeComplex A (n + 1) ⟶ K) :
    K.d k (k + 1)
        (eqToHom (congrArg K.X hk) (serreCubeTopCellImage A K (n + 1) f)) =
      ∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
        (eqToHom (congrArg K.X ht)
            (serreCubeTopCellImage A K n ((serreCubeFace A false n i).hom ≫ f)) -
          eqToHom (congrArg K.X ht)
            (serreCubeTopCellImage A K n ((serreCubeFace A true n i).hom ≫ f))) := by
  exact (complexDifferential_degree_transport A K hk ht
    (serreCubeTopCellImage A K (n + 1) f)).trans
      ((congrArg (fun w => eqToHom (congrArg K.X ht) w)
        (serreCubeTopCellImage_d A K n f)).trans
          (by simp only [map_sum, Units.smul_def, map_zsmul, map_sub]))

end SerrePositivity.KST.SConstruction

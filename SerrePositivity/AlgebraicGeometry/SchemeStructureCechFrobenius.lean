module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedFrobenius
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechComparison

/-!
概要：構造層の実際の p 乗を、Čech の係数前層の射として扱う。
方針：基底環での p = 0 を切断へ移し、零環になる開集合も一様に扱う。
規約：各開集合の切断環に Nontrivial や ExpChar を要求しない。
使われ方：共通アフィン細分と Frobenius の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) {R : Type u} [CommRing R]
variable (φ : R →+* Γ(Y, ⊤)) (p : ℕ) (hp : p.Prime) [ExpChar R p]
variable (hz : (p : R) = 0)

include φ hz in
/-- 基底の p = 0 は、空の開も含めすべての切断環へ移る。 -/
theorem schemeStructurePrimeCast (U : Y.Opens) : (p : Γ(Y, U)) = 0 := by
  let ψ := ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom).comp φ
  rw [← map_natCast ψ p, hz, map_zero]

/-- 構造層の切断の実際の Frobenius。基底のスカラー作用を p 乗でねじる。 -/
def schemeStructureCechFrobeniusCoefficient :
    schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φ ⟶
      schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars (φ.comp (frobenius R p)) where
  app U := ModuleCat.ofHom
    (X := (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φ).obj U)
    (Y := (schemeStructureCechPresheaf Y ⋙
      ModuleCat.restrictScalars (φ.comp (frobenius R p))).obj U)
    { toFun := projectivePrimePowerRingHom p hp (schemeStructurePrimeCast Y φ p hz U.unop)
      map_add' := (projectivePrimePowerRingHom p hp
        (schemeStructurePrimeCast Y φ p hz U.unop)).map_add
      map_smul' := by
        intro r x
        let ψ : R →+* Γ(Y, U.unop) :=
          ((Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom).comp φ
        let y : Γ(Y, U.unop) := x
        change (ψ r * y) ^ p = ψ (r ^ p) * y ^ p
        rw [mul_pow, map_pow] }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let y : Γ(Y, U.unop) := x
    change ((Y.presheaf.map i).hom y) ^ p = (Y.presheaf.map i).hom (y ^ p)
    exact (map_pow (Y.presheaf.map i).hom y p).symm

/-- 構造層の Frobenius の各開上の式は p 乗そのもの。 -/
theorem schemeStructureCechFrobeniusCoefficient_apply (U : Y.Opens) (x : Γ(Y, U)) :
    ((schemeStructureCechFrobeniusCoefficient Y φ p hp hz).app (op U)).hom x = x ^ p := rfl

end SerrePositivity.AlgebraicGeometry

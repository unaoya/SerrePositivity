module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientCech
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveModuleMap

/-!
概要：次数付き加群の射を、商環係数の閉厚化の実際の射へ降ろす。
方針：元の商写像を保ち、全射な多項式係数変更で線形性を示す。
規約：元の多項式環へ作用を制限すると以前の商写像と一致する。
使われ方：閉厚化の係数比較の自然性への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M N : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (J : Ideal R) (f : M →ₗ[MvPolynomial ι R] N)
local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) J
local instance : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J
local instance : Algebra (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J)) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).toAlgebra
local instance : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) J

local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficientModule (ι := ι) (M := N) J
local instance : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) (M := N) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) (M := N) J
local instance : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) (M := N) J
local instance : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) (M := N) J
local instance : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) (M := N) J


/-- 実際の閉厚化の商写像を、商係数多項式環上の写像として表す。 -/
def reesClosedCoefficientModuleMap :
    reesAdicProjectiveQuotient (ι := ι) (M := M) J 1 →ₗ[MvPolynomial ι (R ⧸ J)]
      reesAdicProjectiveQuotient (ι := ι) (M := N) J 1 where
  toFun := reesAdicProjectiveQuotientMap J f 1
  map_add' := (reesAdicProjectiveQuotientMap J f 1).map_add
  map_smul' := by
    intro p x
    obtain ⟨a, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective p
    simp only [RingHom.id_apply, reesClosedPolynomialCoefficient_map_smul]
    exact (reesAdicProjectiveQuotientMap J f 1).map_smul a x

/-- 元の多項式環への係数制限で、既存の実際の商写像を回復する。 -/
theorem reesClosedCoefficientModuleMap_restrictScalars :
    (reesClosedCoefficientModuleMap J f).restrictScalars (MvPolynomial ι R) =
      reesAdicProjectiveQuotientMap J f 1 := by
  apply LinearMap.ext
  intro x
  rfl

variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable (hf : ∀ d, ∀ m ∈ G d, f m ∈ H d)
include hf

/-- 商係数の閉厚化の射も、実際の商次数成分を保つ。 -/
theorem reesClosedCoefficientModuleMap_preservesPiece (d : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) J 1)
    (hx : x ∈ reesClosedCoefficientPiece (ι := ι) J G d) :
    reesClosedCoefficientModuleMap J f x ∈ reesClosedCoefficientPiece (ι := ι) J H d :=
  reesAdicProjectiveQuotientMap_preservesPiece J f G H hf 1 d x hx

end SerrePositivity.AlgebraicGeometry

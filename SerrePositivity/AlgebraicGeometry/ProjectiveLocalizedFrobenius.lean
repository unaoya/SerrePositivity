module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction
public import Mathlib.Algebra.CharP.Frobenius

/-!
概要：空の標準開も許して、実際の局所化の Frobenius と分数式を扱う。
方針：p の像が零であることから冪写像を環準同型にし、局所化の冪の公式を使う。
規約：局所化環に Nontrivial や ExpChar を追加しない。
使われ方：次数付き環の構造層の Čech Frobenius と p 倍の分母の指数を接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)

/-- p の像が零であれば、零環も含め p 乗は環準同型である。 -/
def projectivePrimePowerRingHom (hz : (p : A) = 0) : A →+* A where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' x y := by
    rw [add_pow_prime_eq hp, hz, zero_mul, zero_mul, zero_mul, add_zero]

/-- 通常の指数標数の Frobenius と、p が零であることから作った冪写像は一致する。 -/
theorem projectivePrimePowerRingHom_eq_frobenius [ExpChar A p] (hz : (p : A) = 0) :
    projectivePrimePowerRingHom p hp hz = frobenius A p := by
  ext x
  rfl

section Localization
variable {P : Type*} [CommRing P] [Algebra P A] (S : Submonoid P)

/-- 元の係数環で p が零なら、局所化でも p は零。空の標準開の場合も含む。 -/
theorem projectiveLocalized_primeCast_eq_zero (hz : (p : A) = 0) :
    (p : LocalizedModule S A) = 0 := by
  rw [← map_natCast (LocalizedModule.numeratorRingHom (R := P) (S := S)) p, hz, map_zero]

/-- 実際の局所化環の Frobenius。局所化が零環でも定義できる。 -/
def projectiveLocalizedFrobenius (hz : (p : A) = 0) :
    LocalizedModule S A →+* LocalizedModule S A :=
  projectivePrimePowerRingHom p hp (projectiveLocalized_primeCast_eq_zero p S hz)

/-- 局所化の Frobenius は、分子と分母を共に p 乗へ送る。 -/
theorem projectiveLocalizedFrobenius_mk (hz : (p : A) = 0) (m : A) (s : S) :
    projectiveLocalizedFrobenius p hp S hz (LocalizedModule.mk m s) =
      LocalizedModule.mk (m ^ p) (s ^ p) :=
  LocalizedModule.mk_pow p m s

end Localization

/-- 分母 fⁿ の p 乗は、同じ f の n*p 冪。 -/
theorem projectiveFrobeniusDenominator_pow {P : Type*} [CommRing P]
    (f : P) (n : ℕ) :
    (projDenominator f n) ^ p = projDenominator f (n * p) := by
  apply Subtype.ext
  exact (pow_mul f n p).symm

/-- 標準開の Frobenius は、元の分母の指数を p 倍にする。 -/
theorem projectiveLocalizedFrobenius_fraction {P : Type*} [CommRing P] [Algebra P A]
    (f : P) (hz : (p : A) = 0) (m : A) (n : ℕ) :
    projectiveLocalizedFrobenius p hp (Submonoid.powers f) hz
        (LocalizedModule.mk m (projDenominator f n)) =
      LocalizedModule.mk (m ^ p) (projDenominator f (p * n)) := by
  rw [projectiveLocalizedFrobenius_mk, projectiveFrobeniusDenominator_pow, Nat.mul_comm n p]

/-- 局所化の制限は、係数環の作用による分子の冪の計算と可換。 -/
theorem projectiveModuleAwayRestriction_pow {P : Type*} [CommRing P] [Algebra P A]
    {f g a : P} (ha : g = f * a) (z : LocalizedModule (Submonoid.powers f) A) :
    projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) (z ^ p) =
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z) ^ p := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨s, k, rfl⟩ := s
    change projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        ((LocalizedModule.mk m (projDenominator f k)) ^ p) =
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk m (projDenominator f k))) ^ p
    rw [LocalizedModule.mk_pow, projectiveFrobeniusDenominator_pow,
      projectiveModuleAwayRestriction_mk ha, projectiveModuleAwayRestriction_mk ha,
      LocalizedModule.mk_pow, projectiveFrobeniusDenominator_pow]
    congr 1
    simp only [Algebra.smul_def, mul_pow, map_pow, pow_mul]

/-- 実際の局所化の Frobenius は、標準開を狭める制限と可換。 -/
theorem projectiveLocalizedFrobenius_restriction {P : Type*} [CommRing P] [Algebra P A]
    {f g a : P} (ha : g = f * a) (hz : (p : A) = 0)
    (z : LocalizedModule (Submonoid.powers f) A) :
    projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (projectiveLocalizedFrobenius p hp (Submonoid.powers f) hz z) =
      projectiveLocalizedFrobenius p hp (Submonoid.powers g) hz
        (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z) :=
  projectiveModuleAwayRestriction_pow p ha z

section Semilinearity
variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
variable [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable [ExpChar R p]

/-- 実際の局所化の Frobenius は、元の基底環の Frobenius について半線形。 -/
def projectiveLocalizedFrobeniusSemilinear (S : Submonoid P) (hz : (p : A) = 0) :
    LocalizedModule S A →ₛₗ[frobenius R p] LocalizedModule S A where
  toFun := projectiveLocalizedFrobenius p hp S hz
  map_add' := (projectiveLocalizedFrobenius p hp S hz).map_add
  map_smul' r z := by
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      change (r • LocalizedModule.mk m s) ^ p =
        (frobenius R p r) • ((LocalizedModule.mk m s) ^ p)
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_pow,
        LocalizedModule.mk_pow, LocalizedModule.smul'_mk]
      congr 1
      simp only [frobenius_def, Algebra.smul_def, mul_pow, map_pow]

end Semilinearity
end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.CommutativeAlgebra.Almost.Quotient
public import SerrePositivity.LengthAlgebra.AlmostQuotient
public import SerrePositivity.PerfectComplex.NormalizedLengthComap

/-! # 商環の almost 同型から元の長さの一致へ

全射な係数変更の像イデアルについてだけ冪等性を要求する。
元のイデアルの冪等性を仮定せず、係数制限した長さと raw な零化条件を使う。
特に mod p^N の almost 圏に適用するための一般的な接続である。
-/

@[expose] public section
universe u
namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I J : Ideal R) [Fact ((I.map (algebraMap R S)) * (I.map (algebraMap R S)) =
      I.map (algebraMap R S))]
    (lam : NormalizedLength R J)

/-- 商環で almost 同型な冪ねじれ加群の、元の環への係数制限で測った長さは一致する。
元の環で almost zero が長さ零となる条件を、全射係数変更と短完全列の加法性で移す。 -/
theorem length_eq_of_almost_iso_baseChange
    (hs : Function.Surjective (algebraMap R S))
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    {M N : PowTorsionModule (J.map (algebraMap R S))}
    (e : (Almost.torsionLocalization (I.map (algebraMap R S))
      (J.map (algebraMap R S))).obj M ≅
      (Almost.torsionLocalization (I.map (algebraMap R S))
        (J.map (algebraMap R S))).obj N) :
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len M.obj =
      (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len N.obj := by
  apply length_eq_of_almost_iso (I.map (algebraMap R S)) (J.map (algebraMap R S))
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl) _ e
  intro X hX
  let := Module.compHom X.obj (algebraMap R S)
  let : IsScalarTower R S X.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hIRX : Almost.IsAlmostZero I X.obj :=
    (Almost.isAlmostZero_map_iff_of_surjective I hs).mp hX
  let XR : PowTorsionModule J :=
    ⟨(ModuleCat.restrictScalars (algebraMap R S)).obj X.obj,
      IsPowTorsion.comap (algebraMap R S) le_rfl X.obj X.property⟩
  exact hzero XR hIRX

/-- 商環の全加群の almost 圏で同型な対象についても、元の長さは一致する。
原典の M^a≃N^a を、冪ねじれ部分圏内の同型だけに制限しない。 -/
theorem length_eq_of_full_almost_iso_baseChange
    (hs : Function.Surjective (algebraMap R S))
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    {M N : PowTorsionModule (J.map (algebraMap R S))}
    (e : (Almost.localization (I.map (algebraMap R S))).obj M.obj ≅
      (Almost.localization (I.map (algebraMap R S))).obj N.obj) :
    (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len M.obj =
      (lam.comap (algebraMap R S) (J.map (algebraMap R S)) le_rfl).len N.obj := by
  obtain ⟨e'⟩ := Almost.isTorsionIsomorphic_of_iso
    (I.map (algebraMap R S)) (J.map (algebraMap R S)) M N e
  exact length_eq_of_almost_iso_baseChange I J lam hs hzero e'

end SerrePositivity.LengthAlgebra

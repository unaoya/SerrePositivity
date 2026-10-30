module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic

/-! # CLMST の基底に対する有限エタールな開集合

正則局所環から標数零の整域への有限単射拡大について、基底環の非零元を一つ
反転して有限エタール拡大を得る。正則局所環の整域性と、有限拡大の一般点での
エタール性は証明済みの可換環論を使う。完備性や perfectoidization の引用は使わず、
標準局所化上の代数構造を明示する。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST

/-- CLMST で用いる有限拡大は、基底環のある非零元の反転後に有限エタールとなる。
局所化間の作用は元の代数写像を局所化した標準の awayAlgebra である。 -/
theorem exists_finite_etale_away (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsDomain D] [CharZero D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) :
    ∃ g : A, g ≠ 0 ∧
      let _ := GenericEtale.awayAlgebra A D g
      Module.Finite (Localization.Away g) (Localization.Away (algebraMap A D g)) ∧
        Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)) := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  exact GenericEtale.exists_finite_etale_away_of_charZero A D hinj

end SerrePositivity.CLMST

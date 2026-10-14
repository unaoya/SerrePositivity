module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Field.Subfield.Basic

/-! # 底環を小さくしたときの通常微分の非零性

係数制限の自然な写像で普遍微分を比較する。有限性・標数は不要。
-/

@[expose] public section
namespace SerrePositivity

/-- 大きい底環上で非零な普遍微分は、小さい底環上でも非零。 -/
theorem kaehlerDifferential_ne_zero_of_baseRestriction
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (x : T) (hx : KaehlerDifferential.D S T x ≠ 0) :
    KaehlerDifferential.D R T x ≠ 0 := by
  intro h
  apply hx
  have he := congrArg (KaehlerDifferential.map R S T T) h
  simpa only [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
    map_zero] using he

/-- 部分体の包含を実際の係数制限の塔にして、微分の非零性を小さい部分体へ移す。 -/
theorem kaehlerDifferential_subfield_ne_zero_of_le
    {K : Type*} [Field K] (R S : Subfield K) (hRS : R ≤ S)
    (x : K) (hx : KaehlerDifferential.D S K x ≠ 0) :
    KaehlerDifferential.D R K x ≠ 0 := by
  let : Algebra R S := (Subfield.inclusion hRS).toAlgebra
  let : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
  exact kaehlerDifferential_ne_zero_of_baseRestriction R S K x hx

end SerrePositivity

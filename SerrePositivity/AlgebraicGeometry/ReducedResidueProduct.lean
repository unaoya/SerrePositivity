module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
概要：被約環を全素点の剰余体の積へ埋め込む。
方針：各剰余体への射の核はその素イデアルで、全素イデアルの共通部分は冪零元。
規約：零環では空の積を許し、非自明性を仮定しない。
使われ方：Rydh 3.10 の一般のアフィン基底に使う、極小素イデアル集合が準コンパクトな整拡大。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable (A : Type u) [CommRing A]

/-- 全素点の剰余体の積。 -/
abbrev ResidueFieldProduct := ∀ q : PrimeSpectrum A, q.asIdeal.ResidueField

/-- 各素点の剰余体への標準射をまとめた環準同型。 -/
def reducedResidueProductMap : A →+* ResidueFieldProduct A :=
  RingHom.pi fun q ↦ algebraMap A q.asIdeal.ResidueField

/-- 被約環から剰余体の積への標準射は単射。零環も含む。 -/
theorem reducedResidueProductMap_injective [IsReduced A] :
    Function.Injective (reducedResidueProductMap A) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  apply (Ideal.mem_bot).mpr
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have : J.IsPrime := hJ
  have h := congrFun (RingHom.mem_ker.mp hx) (⟨J, hJ⟩ : PrimeSpectrum A)
  exact (Ideal.algebraMap_residueField_eq_zero).mp h

end SerrePositivity.AlgebraicGeometry

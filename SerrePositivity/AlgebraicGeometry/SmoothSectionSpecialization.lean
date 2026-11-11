module

public import SerrePositivity.AlgebraicGeometry.ConnectedEtaleDomain
public import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
概要：整閉局所整域上の滑らかなアフィン射の二つの切断について、ファイバーの連結成分を比べる。
方針：一般ファイバーで切断を分ける冪等元は全空間に持ち上がり、閉ファイバーでも切断を分ける。
規約：切断のファイバー上の点は、体への評価写像の核で表す。
使われ方：切断を通るファイバー成分の開性を示す際の特殊化の判定。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
概要：アフィン射の切断を基底変更後の代数上の評価写像にする。
方針：切断と底変換先の恒等写像をテンソルする。
規約：基底変更先は任意の基底代数でよい。
使われ方：切断のファイバー上の点を定義する。
-/
def sectionFiberEval {A B L : Type*} [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra A L] (s : B →ₐ[A] A) : B ⊗[A] L →ₐ[A] L :=
  (Algebra.TensorProduct.lid A L).toAlgHom.comp
    (Algebra.TensorProduct.map s (AlgHom.id A L))

/--
概要：アフィン射の切断から、基底を体に変えた後のファイバー上の点を作る。
方針：切断を体へ底変換して評価し、その核を取る。
規約：ファイバーの環は元の代数を左に置いたテンソル積で表す。
使われ方：閉ファイバーと一般ファイバーで切断を通る連結成分を比較する。
-/
def sectionPointInTensor {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (L : Type*) [Field L] [Algebra A L] (s : B →ₐ[A] A) : PrimeSpectrum (B ⊗[A] L) :=
  (⊥ : PrimeSpectrum L).comap (sectionFiberEval s).toRingHom

private theorem sectionPointInTensor_mem_basicOpen
    {A B L : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field L] [Algebra A L]
    (s : B →ₐ[A] A) (b : B) :
    sectionPointInTensor L s ∈ PrimeSpectrum.basicOpen (algebraMap B (B ⊗[A] L) b) ↔
      algebraMap A L (s b) ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  change ¬ sectionFiberEval (L := L) s (b ⊗ₜ[A] (1 : L)) ∈ (⊥ : Ideal L) ↔ _
  simp [sectionFiberEval, Algebra.smul_def]

/--
概要：滑らかなアフィン射の二つの切断が閉ファイバーで同じ連結成分を通れば、
一般ファイバーでも同じ連結成分を通る。
方針：一般ファイバーで二点を分ける冪等元を全空間に持ち上げる。
切断への制限は基底上の零か一なので、閉ファイバーでも二点を分けてしまう。
規約：基底は整閉局所整域とし、Noether 性を仮定しない。
使われ方：滑らかな場合の Stacks 055Q の付値環上での判定。
-/
theorem sectionPointInTensor_mem_genericComponent_of_mem_closedComponent
    {A B K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (s t : B →ₐ[A] A)
    (h : sectionPointInTensor (IsLocalRing.ResidueField A) t ∈
      connectedComponent (sectionPointInTensor (IsLocalRing.ResidueField A) s)) :
    sectionPointInTensor K t ∈ connectedComponent (sectionPointInTensor K s) := by
  let D := B ⊗[A] K
  let k := IsLocalRing.ResidueField A
  let : IsNoetherianRing D := by
    let : Algebra.FiniteType K D := Algebra.FiniteType.equiv
      (inferInstance : Algebra.FiniteType K (K ⊗[A] B))
      (Algebra.TensorProduct.commRight A K B)
    exact Algebra.FiniteType.isNoetherianRing K D
  by_contra h'
  obtain ⟨d, hd, hC⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace (sectionPointInTensor K s))
  obtain ⟨b, ⟨hb, rfl⟩, _⟩ := existsUnique_idempotent_of_smooth_fractionTensor d hd
  have hs : algebraMap A K (s b) ≠ 0 := by
    apply (sectionPointInTensor_mem_basicOpen s b).mp
    change sectionPointInTensor K s ∈ (PrimeSpectrum.basicOpen
      (algebraMap B (B ⊗[A] K) b) : Set (PrimeSpectrum D))
    rw [← hC]
    exact mem_connectedComponent
  have ht : algebraMap A K (t b) = 0 := by
    by_contra ht'
    apply h'
    rw [hC]
    exact (sectionPointInTensor_mem_basicOpen t b).mpr ht'
  have hs1 : s b = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp (hb.map s)).resolve_left
      (fun hz => hs (by rw [hz, map_zero]))
  have ht0 : t b = 0 :=
    (IsFractionRing.injective A K) (by simpa only [map_zero] using ht)
  let e := algebraMap B (B ⊗[A] k) b
  have he : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (B ⊗[A] k))) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, hb.map _, rfl⟩
  have hs' : sectionPointInTensor k s ∈ PrimeSpectrum.basicOpen e :=
    (sectionPointInTensor_mem_basicOpen s b).mpr (by rw [hs1, map_one]; exact one_ne_zero)
  exact (sectionPointInTensor_mem_basicOpen t b).mp (he.connectedComponent_subset hs' h)
    (by rw [ht0, map_zero])

end SerrePositivity.AlgebraicGeometry

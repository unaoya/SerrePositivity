module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
概要：完全な任意の係数への普遍Čech完全性の代入と、零環を含むtensorの完全性。
方針：同じ底変換のtensor結合同型を用い、零環のときは直接p乗の全単射性を示す。
規約：底変換に平坦性や非零性を仮定しない。
使われ方：2iのU07・U09。BM18 Proposition 4.8の構造層版の係数移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画U07：元の射を保つ完全係数の比較。 -/
theorem perfectRingCechUniversalExact_baseChange (p : ℕ)
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [PerfectRing T p] (f : A →+* B) (g : A →+* T)
    (hf : PerfectRingCechUniversalExact p f) :
    PerfectRingCechUniversalExact p (arcBaseChangeHom f g) := by
  intro S _ _ h
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI : Algebra A S := (h.comp g).toAlgebra
  let X := Under.mk (CommRingCat.ofHom f)
  let G := CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of T)
  let H := CommRingCat.tensorProd (CommRingCat.of T) (CommRingCat.of S)
  let K := CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)
  let eg := CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of T)
  let eh := CommRingCat.tensorProdIsoPushout (CommRingCat.of T) (CommRingCat.of S)
  let ek := CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of S)
  let η : K ≅ G ⋙ H := ek ≪≫
    Under.pushoutComp (CommRingCat.ofHom g) (CommRingCat.ofHom h) ≪≫
    Functor.isoWhiskerRight eg.symm (Under.pushout (CommRingCat.ofHom h)) ≪≫
    Functor.isoWhiskerLeft G eh.symm
  let e := η.app X
  let q : Arrow.mk (K.obj X).hom ≅ Arrow.mk (H.obj (G.obj X)).hom :=
    Arrow.isoMk (Iso.refl _) ((Under.forget (CommRingCat.of S)).mapIso e) (by
      simpa using (Under.w e.hom).symm)
  have hK : Cech.IsCechExact (Arrow.mk (K.obj X).hom) := hf S (h.comp g)
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso q)).mp hK

/-- 計画U09：元の射を保つ完全係数の比較。 -/
theorem perfectTensor_of_primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    (A T B : Type u) [CommRing A] [CommRing T] [CommRing B]
    [Algebra A T] [Algebra A B] [PerfectRing A p] [PerfectRing T p]
    [PerfectRing B p] (hp : (p : A) = 0) : PerfectRing (T ⊗[A] B) p := by
  have hzero {Q : Type u} [CommRing Q] (f : Q →+* T ⊗[A] B) (hT : Subsingleton Q) :
      PerfectRing (T ⊗[A] B) p := by
    have hz : (0 : T ⊗[A] B) = 1 := by
      rw [← map_zero f, ← map_one f, hT.elim (0 : Q) 1]
    let h := subsingleton_of_zero_eq_one hz
    exact ⟨⟨fun _ _ _ => h.elim _ _, fun x => ⟨0, h.elim _ _⟩⟩⟩
  rcases subsingleton_or_nontrivial T with hD | hD
  · exact hzero (algebraMap T (T ⊗[A] B)) hD
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact hzero (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom hB
  let : Nontrivial A := (algebraMap A T).domain_nontrivial
  have hd : (p : T) = 0 := by rw [← map_natCast (algebraMap A T), hp, map_zero]
  have hb : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hp, map_zero]
  let : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
  let : CharP T p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hd
  let : CharP B p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hb
  exact perfectCoefficientTensor_perfectRing p A T B

/-- 計画U08：忠実平坦な拡大上の切断で任意の係数の完全性を反映する。 -/
theorem perfectRingCechUniversalExact_of_flat_factor (p : ℕ)
    {A B W : Type u} [CommRing A] [CommRing B] [CommRing W]
    (f : A →+* B) (e : A →+* W) (l : B →+* W)
    (he : e.FaithfullyFlat) (hl : l.comp f = e) :
    PerfectRingCechUniversalExact p f := by
  intro T _ _ g
  letI := f.toAlgebra
  letI := e.toAlgebra
  letI := g.toAlgebra
  letI : Module.FaithfullyFlat A W := he
  let S := T ⊗[A] W
  let iW : W →+* S := (Algebra.TensorProduct.includeRight : W →ₐ[A] S).toRingHom
  have hc (a : A) : (algebraMap T S) (algebraMap A T a) =
      (iW.comp l) (algebraMap A B a) := by
    change g a ⊗ₜ[A] (1 : W) = (1 : T) ⊗ₜ[A] l (f a)
    have hla := RingHom.congr_fun hl a
    change l (f a) = e a at hla
    rw [hla]
    change (algebraMap A T a) ⊗ₜ[A] (1 : W) = (1 : T) ⊗ₜ[A] algebraMap A W a
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := A) a (1 : T) (1 : W))
  let r := coefficientTensorLift (algebraMap T S) (iW.comp l) hc
  let BT := Under.mk (CommRingCat.ofHom (arcBaseChangeHom f g))
  let ST := Under.mk (CommRingCat.ofHom (algebraMap T S))
  have hr : BT.hom ≫ CommRingCat.ofHom r = ST.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change r (t ⊗ₜ[A] (1 : B)) = algebraMap T S t
    rw [coefficientTensorLift_tmul, map_one, mul_one]
  have hff : (algebraMap T S).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hb := Cech.isCechExact_baseChange_of_map BT ST (Under.homMk (CommRingCat.ofHom r) hr)
  letI : Algebra (CommRingCat.of T) ST.right := CommRingCat.instAlgebraCarrierRight ST
  letI : Module.FaithfullyFlat (CommRingCat.of T) ST.right := hff
  exact (Cech.isCechExact_baseChange_iff ST.right BT).mp hb

end SerrePositivity.AlgebraicGeometry.ArcRouteB

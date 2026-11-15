module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.CompletedTensorFlat
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalFiniteResidue
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 有界な係数への完備テンソル積の忠実性

## 概要
p 完全忠実平坦な代数の完備底変換は、有界な係数環上でも p 完全忠実平坦。
## 方針
完全平坦性は既存の導来模型で、忠実性は実 mod p の通常テンソル比較で示す。
## 規約
BS 著者版 Proposition 7.10。通常の平坦性への置き換えや Fil₀ の分裂を使わない。
## 使われ方
有限 T と完備余極限の単位の忠実性。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A]

/-- 有界な係数環への実 p 完備テンソル積は、p 完全忠実平坦性を保つ。 -/
theorem completedTensorPrincipal_isCompletelyFaithfullyFlat (p : ℕ)
    (hA : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) A)
    (hB : ∃ N : ℕ, ∀ (n : ℕ) (b : B), (p : B)^n * b = 0 → (p : B)^N * b = 0) :
    let T := B ⊗[R] A
    letI := principalCompletionCommRing T (p : T)
    letI : Algebra B (PrincipalCompletionH0 T (p : T)) :=
      ((principalCompletionUnitRingHom T (p : T)).comp (algebraMap B T)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) (PrincipalCompletionH0 T (p : T)) := by
  let T := B ⊗[R] A
  let H := PrincipalCompletionH0 T (p : T)
  letI := principalCompletionCommRing T (p : T)
  let j : T →+* H := principalCompletionUnitRingHom T (p : T)
  let l := j.comp (algebraMap B T)
  letI : Algebra B H := l.toAlgebra
  let I : Ideal R := Ideal.span {(p : R)}
  let J : Ideal B := Ideal.span {(p : B)}
  let U := R ⧸ I
  let E := B ⧸ J
  let q := Ideal.Quotient.mk J
  have hIJ : I.map (algebraMap R B) ≤ J := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let α : U →+* E := Ideal.quotientMap J (algebraMap R B) (Ideal.map_le_iff_le_comap.mp hIJ)
  letI : Algebra U E := α.toAlgebra
  letI : IsScalarTower R U E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨completedTensorPrincipal_isCompletelyFlat R B A p hA.1 hB, ?_⟩
  let JT := J.map (algebraMap B T)
  let JH := J.map l
  have hJT : JT = Ideal.span {(p : T)} := by
    change (Ideal.span {(p : B)}).map (algebraMap B T) = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hJH : JH = (Ideal.span {(p : T)}).map j := by
    change J.map (j.comp (algebraMap B T)) = _
    rw [← Ideal.map_map]
    change Ideal.map j JT = _
    rw [hJT]
  obtain ⟨e00, he00⟩ := exists_principalCompletion_modPrime_equiv T p
  let e0 : (H ⧸ (Ideal.span {(p : T)}).map j) ≃+* T ⧸ Ideal.span {(p : T)} := e00
  have he0 (x : T) : e0 (Ideal.Quotient.mk _ (j x)) = Ideal.Quotient.mk _ x := he00 x
  let e1 : (H ⧸ JH) ≃+* T ⧸ JT :=
    ((Ideal.quotEquivOfEq hJH).trans e0).trans (Ideal.quotEquivOfEq hJT.symm)
  have he1 (x : T) : e1 (Ideal.Quotient.mk JH (j x)) = Ideal.Quotient.mk JT x := by
    change (Ideal.quotEquivOfEq hJT.symm) (e0 (Ideal.Quotient.mk _ (j x))) = _
    rw [he0]
    rfl
  let e2 := (Algebra.TensorProduct.quotientTensorEquiv (R := R) B A B J).symm
  letI : Algebra E (H ⧸ JH) := adicQuotientAlgebra J H
  let er := e1.trans e2.toRingEquiv
  let e3 : (H ⧸ JH) ≃ₗ[E] E ⊗[R] A :=
    { er.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
        change er (Ideal.Quotient.mk JH (l b) * x) = (q b) • er x
        have hs : (q b) • er x = (q b ⊗ₜ[R] (1 : A)) * er x := Algebra.smul_def _ _
        rw [hs, map_mul]
        congr 1
        change e2 (e1 (Ideal.Quotient.mk JH (j (algebraMap B T b)))) = _
        rw [he1]
        exact Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul B A B J b 1 }
  let e4 := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor H J).symm.toLinearEquiv
  let e5 := (TensorProduct.AlgebraTensorModule.cancelBaseChange R U E E A).symm
  letI : Module.FaithfullyFlat U (U ⊗[R] A) := hA.2
  letI : Module.FaithfullyFlat E (E ⊗[U] (U ⊗[R] A)) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (e4.trans (e3.trans e5))

end SerrePositivity.BhattScholze.Semiperfectoid

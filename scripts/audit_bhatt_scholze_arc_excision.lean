import SerrePositivity.BhattScholze.Perfectoidization.Interface.Excision
import SerrePositivity.BhattScholze.Perfectoidization.Excision

/-!
Cor 8.12 の指定された一つの引用と、その受渡し型の監査。
これは文献入力なので assert_no_sorry の対象にはしない。
公理出力は標準三公理と sorryAx の範囲、sorries 出力はこの引用に限られることを検査する。
-/

set_option pp.fullNames true

#print axioms SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback
#print sorries SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback

open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
universe u

-- ユーザー指定の完全な型を独立に再掲し、そのまま適用できることを検査する。
example
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) → ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D} {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map))) := by
  exact BhattScholze.Inputs.perfectoidization_excision_isPullback
    R S T p hR f I hS hT hI harc hC hD hQ hE

-- 二つの系は新しい sorry を持たず、上の ArcExcision 一件だけに到達する。
#print axioms SerrePositivity.BhattScholze.klCanonicalExcisionSquare_of_excision
#print sorries SerrePositivity.BhattScholze.klCanonicalExcisionSquare_of_excision
#print axioms SerrePositivity.BhattScholze.klCanonicalExcisionSquare_of_integral_away
#print sorries SerrePositivity.BhattScholze.klCanonicalExcisionSquare_of_integral_away

-- 整拡大版の受渡し型と引数順を、CLMST を import せずに検査する。
example
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (q : A →ₐ[R] B) [@Algebra.IsIntegral A B _ _ q.toRingHom.toAlgebra]
    (a : R) (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hA : IsModuleComplete A (p : A) (ModuleCat.of A A))
    (hB : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hI : IsModuleComplete A (p : A) (ModuleCat.of A (Ideal.span {algebraMap R A a})))
    (haway : Function.Bijective (Localization.awayMap q.toRingHom (algebraMap R A a))) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
      (CommRingCat.ofHom (BhattScholze.perfectoidizationClosedSideProjection hf
        (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (BhattScholze.perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
      (CommRingCat.ofHom (BhattScholze.perfectoidizationClosedComparison hf hg q.toRingHom
        (Ideal.span {algebraMap R A a}))) :=
  BhattScholze.klCanonicalExcisionSquare_of_integral_away
    R p hR A B C D q a f g hf hg hA hB hI haway

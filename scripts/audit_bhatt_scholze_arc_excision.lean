import SerrePositivity.BhattScholze.Inputs.ArcExcision

/-!
Cor 8.12 の指定された一つの引用と、その受渡し型の監査。
これは文献入力なので assert_no_sorry の対象にはしない。
公理出力は標準三公理と sorryAx の範囲、sorries 出力はこの引用に限られることを検査する。
-/

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

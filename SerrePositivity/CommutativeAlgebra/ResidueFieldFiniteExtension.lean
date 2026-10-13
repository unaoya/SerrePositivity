module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldSuccessor

/-! # 有限生成剰余体拡大

共通の後続段を有限回適用し、最後に一度だけ完備化する。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 有限生成中間体を、Noether平坦局所拡大の指定剰余体として構成する。
Mathlibの単生成拡大による帰納法を使い、各段では完備化しない。 -/
theorem exists_noetherian_flat_local_extension_of_fg_intermediateField
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (L : IntermediateField (ResidueField B) K) (hL : L.FG) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* L,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) L x := by
  classical
  refine IntermediateField.induction_on_adjoin_fg (motive := fun L ↦
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* L,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) L x)
    ?_ ?_ L hL
  · let e := (IntermediateField.botEquiv (ResidueField B) K).symm
    refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, e.toRingEquiv, ?_⟩
    · simp
    · intro x
      obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
      rw [ResidueField.map_residue]
      exact e.commutes (residue B b)
  · intro L x ih
    obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hsmax, eS, heS⟩ := ih
    obtain ⟨T, tRing, tLocal, tAlgS, tAlgB, tTower, tHomS, tHomB,
      tFlatS, tFlatB, tNoeth, htmax, hmax, eT, heT, heStep, t, ht⟩ :=
      exists_residueField_successor B S K L eS heS hsmax x
    let : IsNoetherianRing T := tNoeth inferInstance
    exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, tFlatB, hmax, eT, heT⟩

/-- 指定された有限生成体拡大に対応するNoether平坦局所拡大。 -/
theorem exists_noetherian_flat_local_extension_of_fg
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (hK : (⊤ : IntermediateField (ResidueField B) K).FG) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_noetherian_flat_local_extension_of_fg_intermediateField B K ⊤ hK
  let q := IntermediateField.topEquiv (F := ResidueField B) (E := K)
  refine ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax,
    e.trans q.toRingEquiv, ?_⟩
  intro x
  change q (e (ResidueField.map (algebraMap B S) x)) = _
  rw [he]
  exact q.commutes x

/-- 外部引用1の有限生成体拡大版。最後に一度だけ完備化する。
一般の体拡大の引用や、R3/R4の有向極限の証明には依存しない。 -/
theorem exists_complete_flat_local_extension_of_fg
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (hK : (⊤ : IntermediateField (ResidueField B) K).FG) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_noetherian_flat_local_extension_of_fg B K hK
  obtain ⟨C, cRing, cLocal, cNoeth, cComplete, cAlg, cHom, cFlat, hcmax, eC, heC, c, hc⟩ :=
    exists_complete_flat_local_extension_with_residue B S K hmax e he 0 0 (map_zero e)
  exact ⟨C, cRing, cLocal, cNoeth, cComplete, cAlg, cHom, cFlat, hcmax, eC, heC⟩

/-- 有限個の指定体生成元から、完備Noether平坦局所拡大を構成する。
空集合も許し、その場合は帰納法の基底から完備化する。 -/
theorem exists_complete_flat_local_extension_of_finset
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (s : Finset K) (hs : IntermediateField.adjoin (ResidueField B) (s : Set K) = ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  apply exists_complete_flat_local_extension_of_fg B K
  rw [← hs]
  exact IntermediateField.fg_adjoin_finset s

/-- Mathlibの有限生成体拡大の型クラスから適用する入口。 -/
theorem exists_complete_flat_local_extension_of_essFiniteType
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    [Algebra.EssFiniteType (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  exact exists_complete_flat_local_extension_of_fg B K
    (IntermediateField.fg_top_iff.mpr inferInstance)

end SerrePositivity

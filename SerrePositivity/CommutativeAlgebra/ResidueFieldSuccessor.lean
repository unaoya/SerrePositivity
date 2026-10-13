module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldSimpleExtension

/-! # 剰余体拡大の図式の後続段

構成済みの基底上の平坦局所拡大に対し、指定剰余体へ一元を加える。
旧段からの写像と、新しい基底上の構造を同時に構成し、剰余体写像の両立を保持する。
Noether性は不要なので、極限段の後にも適用できる。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 構成済みの局所拡大の剰余体へ一元を加える後続段。
旧段からの実際の係数写像、その平坦性・局所性、基底からの合成、剰余体の両立を供給する。 -/
theorem exists_residueField_successor
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (L : IntermediateField (ResidueField B) K)
    (eS : ResidueField S ≃+* L)
    (heS : ∀ y, eS (ResidueField.map (algebraMap B S) y) = algebraMap (ResidueField B) L y)
    (hsmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S) (a : K) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T)
      (_ : Algebra S T) (_ : Algebra B T) (_ : IsScalarTower B S T)
      (_ : IsLocalHom (algebraMap S T)) (_ : IsLocalHom (algebraMap B T)),
      Module.Flat S T ∧ Module.Flat B T ∧ (IsNoetherianRing S → IsNoetherianRing T) ∧
      (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ∧
      (maximalIdeal B).map (algebraMap B T) = maximalIdeal T ∧
      ∃ eT : ResidueField T ≃+* IntermediateField.adjoin L {a},
        (∀ y, eT (ResidueField.map (algebraMap B T) y) =
          algebraMap (ResidueField B) (IntermediateField.adjoin L {a}) y) ∧
        (∀ y, eT (ResidueField.map (algebraMap S T) y) =
          algebraMap L (IntermediateField.adjoin L {a}) (eS y)) ∧
        ∃ t : T, eT (residue T t) = IntermediateField.AdjoinSimple.gen L a := by
  let E := IntermediateField.adjoin L {a}
  let : Algebra (ResidueField S) E := ((algebraMap L E).comp eS.toRingHom).toAlgebra
  have hgen : IntermediateField.adjoin (ResidueField S)
      {IntermediateField.AdjoinSimple.gen L a} = ⊤ :=
    adjoin_eq_top_of_scalar_equiv eS (fun _ ↦ rfl) _ (adjoin_simple_gen_eq_top L K a)
  obtain ⟨T, tRing, tLocal, tAlg, tHom, tFlat, tNoeth, htmax, eT, heT, t, ht⟩ :=
    exists_flat_local_extension_of_simple_generator S E
      (IntermediateField.AdjoinSimple.gen L a) hgen
  let : Algebra B T := ((algebraMap S T).comp (algebraMap B S)).toAlgebra
  let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : IsLocalHom (algebraMap B T) := by
    rw [IsScalarTower.algebraMap_eq B S T]
    infer_instance
  let : Module.Flat B T := Module.Flat.trans B S T
  have hmax : (maximalIdeal B).map (algebraMap B T) = maximalIdeal T := by
    rw [IsScalarTower.algebraMap_eq B S T, ← Ideal.map_map, hsmax]
    exact htmax
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, tFlat, inferInstance, tNoeth, htmax, hmax, eT, ?_, heT, t, ht⟩
  intro y
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) y
  rw [ResidueField.map_residue]
  change eT (residue T (algebraMap S T (algebraMap B S b))) = _
  rw [← ResidueField.map_residue, heT]
  change algebraMap L E (eS (residue S (algebraMap B S b))) = _
  rw [← ResidueField.map_residue, heS]
  rfl

end SerrePositivity

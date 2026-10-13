module

public import SerrePositivity.LengthAlgebra.AlmostBaseChange

/-! # 零化イデアルで割った作用による almost 長さ比較

元の環の任意の加群が K で消えるとき、具体的な R/K 作用を構成して比較する。
商環上で almost 同型という仮定は、全加群の実際の局所化圏の同型である。
係数制限した長さは元の長さと一致するため、結論を元の加群について述べられる。
像イデアルの冪等性と almost 零加群の長さ零性は明示的な仮定として受け取る。
-/

@[expose] public section
universe u
namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R]

/-- K が加群を零化するとき、構成した商環作用に沿う長さは元の長さと一致する。 -/
@[simp] theorem quotient_comap_len (K J : Ideal R) (lam : NormalizedLength R J)
    (M : Type u) [AddCommGroup M] [Module R M] (hK : Almost.IsAlmostZero K M) :
    let _ := Almost.quotientModule K M hK
    (lam.comap (Ideal.Quotient.mk K) (J.map (Ideal.Quotient.mk K)) le_rfl).len M =
      lam.len M := by
  let := Almost.quotientModule K M hK
  rfl

/-- 構成した商環作用では、像イデアルの冪ねじれ条件と元の条件は一致する。 -/
theorem isPowTorsion_quotientModule_iff (K J : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hK : Almost.IsAlmostZero K M) :
    let _ := Almost.quotientModule K M hK
    IsPowTorsion (J.map (Ideal.Quotient.mk K)) M ↔ IsPowTorsion J M := by
  let := Almost.quotientModule K M hK
  let := Almost.quotientModule_scalarTower K M hK
  exact Almost.isPowTorsion_map_iff_of_surjective J Ideal.Quotient.mk_surjective

/-- K で零化される元の加群が、商環の全加群の almost 圏で同型なら、元の長さは一致する。
元のイデアル I の冪等性や単一の almost 同型写像の存在を仮定しない。 -/
theorem length_eq_of_quotient_almost_iso (K I J : Ideal R)
    [Fact ((I.map (Ideal.Quotient.mk K)) * (I.map (Ideal.Quotient.mk K)) =
      I.map (Ideal.Quotient.mk K))]
    (lam : NormalizedLength R J)
    (hzero : ∀ X : PowTorsionModule J, Almost.IsAlmostZero I X.obj → lam.len X.obj = 0)
    (M N : ModuleCat.{u} R) (hM : IsPowTorsion J M) (hN : IsPowTorsion J N)
    (hKM : Almost.IsAlmostZero K M) (hKN : Almost.IsAlmostZero K N) :
    let _ := Almost.quotientModule K M hKM
    let _ := Almost.quotientModule K N hKN
    ((Almost.localization (I.map (Ideal.Quotient.mk K))).obj
      (ModuleCat.of (R ⧸ K) M) ≅
      (Almost.localization (I.map (Ideal.Quotient.mk K))).obj
        (ModuleCat.of (R ⧸ K) N)) → lam.len M = lam.len N := by
  let := Almost.quotientModule K M hKM
  let := Almost.quotientModule K N hKN
  dsimp only
  intro e
  let MQ : PowTorsionModule (J.map (Ideal.Quotient.mk K)) :=
    ⟨ModuleCat.of (R ⧸ K) M, (isPowTorsion_quotientModule_iff K J M hKM).mpr hM⟩
  let NQ : PowTorsionModule (J.map (Ideal.Quotient.mk K)) :=
    ⟨ModuleCat.of (R ⧸ K) N, (isPowTorsion_quotientModule_iff K J N hKN).mpr hN⟩
  have heq := length_eq_of_full_almost_iso_baseChange I J lam
    (S := R ⧸ K) Ideal.Quotient.mk_surjective hzero (M := MQ) (N := NQ) e
  exact (quotient_comap_len K J lam M hKM).symm.trans
    (heq.trans (quotient_comap_len K J lam N hKN))

end SerrePositivity.LengthAlgebra

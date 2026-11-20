module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.QuotientKernelLift

/-!
概要：KST §5、Stacks 05D3 の入れ子の剰余の間で整合する右逆の一段。
方針：整合性条件を満たす元の部分加群からの全射を、終域の射影性で分裂させる。
規約：全射の始域の射影性は不要。小さいイデアルによる終域の剰余の射影性を使う。
使われ方：完備化の分裂に必要な整合的な各冪剰余の右逆。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：入れ子の剰余の右逆を、小さいイデアルの剰余で整合する右逆へ持ち上げる。
方針：整合性条件の核を商環上の部分加群とし、元の核による誤差補正で全射性を示す。
規約：KST §5、Stacks 05D3、小さいイデアルの終域剰余だけに射影性を要求する。
使われ方：各冪剰余の右逆の帰納的な構成。
-/
theorem exists_compatible_reduction_section
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (I J : Ideal R) (hJI : J ≤ I)
    [Module.Projective (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))]
    (s : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R]
      (F ⧸ (I • (⊤ : Submodule R F))))
    (hs : ((π.reduceModIdeal I).restrictScalars R).comp s = LinearMap.id) :
    ∃ s' : (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R]
        (F ⧸ (J • (⊤ : Submodule R F))),
      ((π.reduceModIdeal J).restrictScalars R).comp s' = LinearMap.id ∧
      (Submodule.mapQ (J • (⊤ : Submodule R F)) (I • (⊤ : Submodule R F))
        LinearMap.id (Submodule.smul_mono_left hJI)).comp s' =
      s.comp (Submodule.mapQ (J • (⊤ : Submodule R M)) (I • (⊤ : Submodule R M))
        LinearMap.id (Submodule.smul_mono_left hJI)) := by
  let QFJ := J • (⊤ : Submodule R F)
  let QMJ := J • (⊤ : Submodule R M)
  let QFI := I • (⊤ : Submodule R F)
  let QMI := I • (⊤ : Submodule R M)
  let tF := Submodule.mapQ QFJ QFI LinearMap.id (Submodule.smul_mono_left hJI)
  let tM := Submodule.mapQ QMJ QMI LinearMap.id (Submodule.smul_mono_left hJI)
  let πJ := π.reduceModIdeal J
  let πI := π.reduceModIdeal I
  let D := tF - s.comp (tM.comp (πJ.restrictScalars R))
  let T : Submodule (R ⧸ J) (F ⧸ QFJ) :=
    { carrier := LinearMap.ker D
      zero_mem' := (LinearMap.ker D).zero_mem
      add_mem' := (LinearMap.ker D).add_mem
      smul_mem' := by
        intro a p hp
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change D (r • p) = 0
        change D p = 0 at hp
        rw [map_smul, hp, smul_zero] }
  let πT := πJ.comp T.subtype
  have hπT : Function.Surjective πT := by
    intro m
    obtain ⟨m₀, rfl⟩ := Submodule.mkQ_surjective QMJ m
    obtain ⟨p, rfl⟩ := hπ m₀
    let z := QFI.mkQ p - s (QMI.mkQ (π p))
    have hz : πI z = 0 := by
      have hsp := congrArg (fun f => f (QMI.mkQ (π p))) hs
      change πI (s (QMI.mkQ (π p))) = QMI.mkQ (π p) at hsp
      change πI (QFI.mkQ p - s (QMI.mkQ (π p))) = 0
      rw [map_sub, hsp]
      exact sub_self _
    obtain ⟨k, hk⟩ := exists_kernel_preimage_reduceModIdeal π hπ I z hz
    let q := QFJ.mkQ p - QFJ.mkQ k.val
    have hqπ : πJ q = QMJ.mkQ (π p) := by
      change πJ (QFJ.mkQ p - QFJ.mkQ k.val) = QMJ.mkQ (π p)
      rw [map_sub]
      change QMJ.mkQ (π p) - QMJ.mkQ (π k.val) = _
      rw [k.property, map_zero, sub_zero]
    have hqT : q ∈ T := by
      change D q = 0
      change tF q - s (tM (πJ q)) = 0
      rw [hqπ]
      change (QFI.mkQ p - QFI.mkQ k.val) - s (QMI.mkQ (π p)) = 0
      rw [hk]
      change (QFI.mkQ p - (QFI.mkQ p - s (QMI.mkQ (π p)))) -
        s (QMI.mkQ (π p)) = 0
      rw [sub_sub_cancel, sub_self]
    exact ⟨⟨q, hqT⟩, hqπ⟩
  obtain ⟨r, hr⟩ := Module.projective_lifting_property πT LinearMap.id hπT
  let s' := (T.subtype.comp r).restrictScalars R
  refine ⟨s', ?_, ?_⟩
  · apply LinearMap.ext
    intro m
    exact congrArg (fun f => f m) hr
  · apply LinearMap.ext
    intro m
    have hm := (r m).property
    change D (r m).val = 0 at hm
    have hπm := congrArg (fun f => f m) hr
    change πJ (r m).val = m at hπm
    change tF (r m).val - s (tM (πJ (r m).val)) = 0 at hm
    rw [hπm, sub_eq_zero] at hm
    exact hm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

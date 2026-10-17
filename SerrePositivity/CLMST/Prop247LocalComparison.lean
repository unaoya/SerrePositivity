module

public import SerrePositivity.CLMST.Prop247CommonSquare
public import SerrePositivity.CLMST.Prop247Uniform

/-! # Prop 2.4.7：元の局所分裂と perfectoid 化比較からの実錐零化

局所自由比較と可換式は構成する。残る入力は共通モデルの二つの
元の perfectoid 化比較に関する almost 零化だけである。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- 実共通モデルとその元の perfectoid 化比較の almost 零化から、元の β の錐を零化する。
有限自由比較や共通図式の可換性は仮定せず、元の局所分裂から構成する。 -/
theorem prop247_fixed_cone_of_localized_splitting
    {R A E P Q : Type u} [CommRing R] [IsReduced R] [CommRing A] [CommRing E]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R E] [Algebra R P] [Algebra R Q]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime]
    (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (η : E →ₐ[R] Q) (hη : IsPerfectoidization p η.toRingHom)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (a : A →ₐ[R] E) (b : (Fin r → R) →ₐ[R] E)
    (l : E →ₐ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l.toLinearMap]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i))
    (hv : ∀ y : P, IsPerfectoidization.mapAlgHom hβ hη a y = 0 → d • y = 0)
    (hw : ∀ z : (Fin r → R), η (b z) = 0 → d • z = 0)
    (hcw : ∀ y : Q ⧸ (η.comp b).toLinearMap.range, d • y = 0) :
    ∃ q : ℕ, moduleMapConeScalar R β.toLinearMap (d ^ q) = 0 := by
  obtain ⟨k, u, hsq, hu, _hq⟩ := prop247_exists_perfectoid_common_square
    p β hβ η hη d L r e a b l ha hb
  exact prop247_fixed_cone_of_scaled_common_comparison d r β.toLinearMap u
    (IsPerfectoidization.mapAlgHom hβ hη a).toLinearMap (η.comp b).toLinearMap
    k hsq hu hv hw hcw

end SerrePositivity.CLMST

module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomComplex
/-!
概要：係数 span の Hom 複体に元の斉次合成を制限する。
方針：二変数の線形性と微分の Leibniz 式を反映し、非有界 tensor の普遍性で束ねる。
規約：合成の向きと符号は元の豊穣順を保持する。
使われ方：c′ の実 dg 係数閉包の合成鎖写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

def forwardComponent (x y z : J) (p q n : ℤ) (hn : p + q = n) :
    component source target degree R D value coefficient x y p ⊗
      component source target degree R D value coefficient y z q ⟶
        component source target degree R D value coefficient x z n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun f :=
        { toFun g := ⟨forward R f.val g.val hn, by
            subst n
            exact forward_mem_span source target degree R D value coefficient f.property g.property⟩
          map_add' g g' := by
            apply Subtype.ext
            simp [forward, TensorProduct.tmul_add]
          map_smul' a g := by
            apply Subtype.ext
            simp [forward, TensorProduct.tmul_smul] }
      map_add' f f' := by
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        simp [forward, TensorProduct.add_tmul]
      map_smul' a f := by
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        simp [forward, TensorProduct.smul_tmul] })

lemma forwardComponent_differential (x y z : J) (p q : ℤ) :
    forwardComponent source target degree R D value coefficient x y z p q (p + q) rfl ≫
      componentDifferential source target degree R D value coefficient x z (p + q) =
    (componentDifferential source target degree R D value coefficient x y p ▷
      component source target degree R D value coefficient y z q) ≫
      forwardComponent source target degree R D value coefficient x y z
        (p + 1) q (p + q + 1) (by omega) +
    p.negOnePow • (component source target degree R D value coefficient x y p ◁
      componentDifferential source target degree R D value coefficient y z q) ≫
      forwardComponent source target degree R D value coefficient x y z
        p (q + 1) (p + q + 1) (by omega) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  change differential R (forward R f.val g.val rfl) =
    forward R (differential R f.val) g.val (by omega) +
      p.negOnePow • forward R f.val (differential R g.val) (by omega)
  exact differential_forward R f.val g.val rfl

def homComposition (x y z : J) :
    homComplex source target degree R D value coefficient x y ⊗
      homComplex source target degree R D value coefficient y z ⟶
        homComplex source target degree R D value coefficient x z :=
  tensorLift (forwardComponent source target degree R D value coefficient x y z)
    (by
      intro p q
      simpa only [homComplex, CochainComplex.of_d] using
        forwardComponent_differential source target degree R D value coefficient x y z p q)

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded

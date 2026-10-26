module
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Complexes.Braiding
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
概要：任意次数の変換成分の自然性を、斉次射ごとの条件として扱う。
方針：Koszul 符号を明示し、合成に関する閉性を豊穣結合則から導く。
規約：次数零や閉射だけへ制限しない。
使われ方：D-8 e の同じ実商の元 Hom・ε から全 path への全次数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {E : Type w} [DGCategory R E]

lemma forward_units_smul_first {x y z : E} {p q n : ℤ}
    (s : ℤˣ) (f : GradedHom R x y p) (g : GradedHom R y z q) (hn : p + q = n) :
    forward R (s • f) g hn = s • forward R f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_zsmul]

lemma forward_units_smul_second {x y z : E} {p q n : ℤ}
    (s : ℤˣ) (f : GradedHom R x y p) (g : GradedHom R y z q) (hn : p + q = n) :
    forward R f (s • g) hn = s • forward R f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

/-- 全次数の元の射 f に対する、次数 k の変換成分の自然性。 -/
def homogeneousNaturalityAt (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    {x y : D} {p : ℤ} (f : GradedHom R x y p) : Prop :=
  forward R ((F.map x y).f p f) (a y) rfl =
    (k * p).negOnePow • forward R (a x) ((G.map x y).f p f) (by omega)

lemma homogeneousNaturalityAt_forward (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    {x y z : D} {p q : ℤ} (f : GradedHom R x y p) (g : GradedHom R y z q)
    (hf : homogeneousNaturalityAt R F G a f) (hg : homogeneousNaturalityAt R F G a g) :
    homogeneousNaturalityAt R F G a (forward R f g rfl) := by
  dsimp only [homogeneousNaturalityAt] at hf hg ⊢
  rw [DGFunctor.map_forward, DGFunctor.map_forward]
  rw [forward_assoc_of_sum R _ _ _ rfl rfl rfl, hg, forward_units_smul_second]
  rw [← forward_assoc_of_sum R _ _ _ rfl (by omega) (by omega), hf,
    forward_units_smul_first, forward_assoc_of_sum R _ _ _ (by omega) rfl (by omega)]
  rw [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

def homogeneousNaturalityLeftCochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    Cochain (homObject R D x y) (homObject R E (F.obj x) (G.obj y)) k :=
  Cochain.mk (fun i j hij => (F.map x y).f i ≫
    ModuleCat.ofHom ((TensorProduct.mk R _ _).flip (a y)) ≫
    ιTensorObj (homObject R E (F.obj x) (F.obj y))
      (homObject R E (F.obj y) (G.obj y)) i k j hij ≫
    (eComp (Complex R) (F.obj x) (F.obj y) (G.obj y)).f j)

def homogeneousNaturalityRightCochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    Cochain (homObject R D x y) (homObject R E (F.obj x) (G.obj y)) k :=
  Cochain.mk (fun i j hij => (k * i).negOnePow • ((G.map x y).f i ≫
    ModuleCat.ofHom (TensorProduct.mk R _ _ (a x)) ≫
    ιTensorObj (homObject R E (F.obj x) (G.obj x))
      (homObject R E (G.obj x) (G.obj y)) k i j (by omega) ≫
    (eComp (Complex R) (F.obj x) (G.obj x) (G.obj y)).f j))

lemma homogeneousNaturalityAt_iff_cochain (F G : DGFunctor R D E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k) (x y : D) :
    (∀ (p : ℤ) (f : GradedHom R x y p), homogeneousNaturalityAt R F G a f) ↔
      homogeneousNaturalityLeftCochain R F G a x y =
        homogeneousNaturalityRightCochain R F G a x y := by
  constructor
  · intro h
    apply Cochain.ext
    intro i j hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact h i f
  · intro h p f
    exact congrArg (fun z => z f) (Cochain.congr_v h p (p + k) rfl)

lemma gradedFamilyNaturality_iff_homogeneous (F G : DGFunctor R D E) {K : Complex R}
    (a : ∀ x, K ⟶ homObject R E (F.obj x) (G.obj x)) (x y : D) :
    ((β_ K (homObject R D x y)).hom ≫ (F.map x y ⊗ₘ a y) ≫
        eComp (Complex R) _ _ _ = (a x ⊗ₘ G.map x y) ≫ eComp (Complex R) _ _ _) ↔
      ∀ (k p : ℤ) (t : K.X k) (f : GradedHom R x y p),
        homogeneousNaturalityAt R F G (fun z => (a z).f k t) f := by
  constructor
  · intro h k p t f
    have ht := congrArg (fun m => m.f (p + k)
      (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f))) h
    change (eComp (Complex R) _ _ _).f (p + k)
      ((F.map x y ⊗ₘ a y).f (p + k)
        ((signedSwap K (homObject R D x y)).hom.f (p + k)
          (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f)))) =
      (eComp (Complex R) _ _ _).f (p + k) ((a x ⊗ₘ G.map x y).f (p + k)
        (ιTensorObj K (homObject R D x y) k p (p + k) (by omega) (t ⊗ₜ[R] f))) at ht
    rw [signedSwap_apply] at ht
    simp only [Units.smul_def, map_zsmul] at ht
    rw [tensorMap_apply, tensorMap_apply] at ht
    have h' : (k * p).negOnePow • forward R ((F.map x y).f p f) ((a y).f k t) rfl =
        forward R ((a x).f k t) ((G.map x y).f p f) (by omega) := ht
    have hs := congrArg (fun z => (k * p).negOnePow • z) h'
    rw [smul_smul, Int.units_mul_self, one_smul] at hs
    exact hs
  · intro h
    apply tensorHom_ext
    intro k p n hkn
    have hpn : p + k = n := by omega
    cases hpn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro t f
    change (eComp (Complex R) _ _ _).f (p + k)
      ((F.map x y ⊗ₘ a y).f (p + k)
        ((signedSwap K (homObject R D x y)).hom.f (p + k)
          (ιTensorObj K (homObject R D x y) k p (p + k) hkn (t ⊗ₜ[R] f)))) =
      (eComp (Complex R) _ _ _).f (p + k) ((a x ⊗ₘ G.map x y).f (p + k)
        (ιTensorObj K (homObject R D x y) k p (p + k) hkn (t ⊗ₜ[R] f)))
    rw [signedSwap_apply]
    simp only [Units.smul_def, map_zsmul]
    rw [tensorMap_apply, tensorMap_apply]
    have ht := h k p t f
    change forward R ((F.map x y).f p f) ((a y).f k t) rfl =
      (k * p).negOnePow • forward R ((a x).f k t) ((G.map x y).f p f) (by omega) at ht
    change (k * p).negOnePow • forward R ((F.map x y).f p f) ((a y).f k t) rfl = _
    rw [ht, smul_smul, Int.units_mul_self, one_smul]
    rfl

end SerrePositivity.DifferentialGraded

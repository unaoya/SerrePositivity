module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.HomDegrees
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：元の graded bar の斉次自己作用素を、MC 後の実 bar の全 Hom に移す。
方針：全評価 cochain の成分を保持し、両端の変形後も同じ符号付き自然性を検証する。
規約：移すのは次数付き作用素。微分は実 bar の Hom 微分で計算する。
使われ方：退化作用素の実 bar 上での境界と段階的正規化ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Preadditive DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarEndRebase (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    (moduleHom R D (dgCoherentBarModule R D F hMC) (dgCoherentBarModule R D F hMC)).X q :=
  moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((moduleHomπ R D _ _ x.unop).f q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, dgCoherentBarModule_map_v] using h)

lemma dgCoherentBarEndRebase_π (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) (x : D)
    (i j : ℤ) (hij : i + q = j) :
    ((moduleHomπ R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC) x).f q
      (dgCoherentBarEndRebase R D F hMC q z)).v i j hij =
      ((moduleHomπ R D _ _ x).f q z).v i j hij := by
  rw [dgCoherentBarEndRebase, moduleHomElementMk_π]
  rfl

lemma dgCoherentBarEndRebase_add (q : ℤ)
    (z w : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    dgCoherentBarEndRebase R D F hMC q (z + w) =
      dgCoherentBarEndRebase R D F hMC q z + dgCoherentBarEndRebase R D F hMC q w := by
  apply moduleHomElement_ext R D
  intro x
  simp only [map_add, dgCoherentBarEndRebase, moduleHomElementMk_π]
  apply Cochain.ext
  intro i j hij
  rfl

lemma dgCoherentBarEndRebase_d (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d q (q + 1)
      (dgCoherentBarEndRebase R D F hMC q z) =
    dgCoherentBarEndRebase R D F hMC (q + 1)
      ((moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d q (q + 1) z +
        compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (dgCoherentBarTheta R D F) z rfl +
        (q + 1).negOnePow • compose R
          (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          z (dgCoherentBarTheta R D F) (by omega : 1 + q = q + 1)) := by
  apply moduleHomElement_ext R D
  intro x
  let M := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)
  let θ := (moduleHomπ R D M M x).f 1 (dgCoherentBarTheta R D F)
  have hθ := moduleMaurerCartan_evaluation R D M (dgCoherentBarTheta R D F) hMC x
  have hrebase (p : ℤ) (w : (moduleHom R D M M).X p) :
      (moduleHomπ R D (dgCoherentBarModule R D F hMC)
        (dgCoherentBarModule R D F hMC) x).f p (dgCoherentBarEndRebase R D F hMC p w) =
      maurerCartanRebaseCochain θ θ hθ hθ ((moduleHomπ R D M M x).f p w) := by
    apply Cochain.ext
    intro i j hij
    rw [dgCoherentBarEndRebase_π]
    rfl
  rw [moduleHomElement_d_π, hrebase, hrebase]
  apply (maurerCartanCochainEquiv θ θ hθ hθ (q + 1)).symm.injective
  change maurerCartanForgetCochain θ θ hθ hθ
    (δ q (q + 1) (maurerCartanRebaseCochain θ θ hθ hθ
      ((moduleHomπ R D M M x).f q z))) = _
  rw [maurerCartanHom_δ]
  change _ = (maurerCartanCochainEquiv θ θ hθ hθ (q + 1)).symm
    ((maurerCartanCochainEquiv θ θ hθ hθ (q + 1)) _)
  rw [LinearEquiv.symm_apply_apply]
  dsimp only [M, θ]
  rw [← moduleHomElement_d_π R D q (q + 1) z x,
    ← moduleHomCompose_π R D (dgCoherentBarTheta R D F) z rfl x,
    ← moduleHomCompose_π R D z (dgCoherentBarTheta R D F)
      (by omega : 1 + q = q + 1) x]
  have hadd {A B : ModuleCat.{u} R} (f : A ⟶ B) (a b c : A) (k : ℤˣ) :
      f (a + b + k • c) = f a + f b + k • f c := by
    change f.hom (a + b + k • c) = f.hom a + f.hom b + k • f.hom c
    simp only [map_add, Units.smul_def, map_zsmul]
  exact (hadd ((moduleHomπ R D M M x).f (q + 1)) _ _ _ (q + 1).negOnePow).symm

end SerrePositivity.InfinityCategories

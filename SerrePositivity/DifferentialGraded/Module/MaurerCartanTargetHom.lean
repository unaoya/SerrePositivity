module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartan
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanTargetHom

/-!
概要：標的だけを MC 変形した加群 Hom の全次数係数を、元の Hom と比較する。
方針：各評価の標的だけの cochain 移送を、主 Hom end の全次数自然性で再構成する。
規約：始域加群を固定し、係数 dg 圏だけの Small 仮定を使う。
使われ方：MC 摂動後の bar の終端 HA 成分と元の成分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (N : RightModule R D) (ψ : (moduleHom R D N N).X 1)
  (hψ : (moduleHom R D N N).d 1 2 ψ +
    compose R (x := N) (y := N) (z := N) ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)


lemma moduleMaurerCartan_map_v (x y : Dᵒᵖ) (p : ℤ)
    (a : GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    (((moduleMaurerCartan R D N ψ hψ).map x y).f p a).v i j hij =
      ((N.map x y).f p a).v i j hij := rfl

def moduleMaurerCartanTargetRebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q :=
  moduleHomElementMk R D q
    (fun x => maurerCartanTargetRebaseCochain ((moduleHomπ R D N N x.unop).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x.unop) ((moduleHomπ R D M N x.unop).f q z)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij) (moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [maurerCartanTargetRebaseCochain, Cochain.mk_v, moduleMaurerCartan_map_v] using h)

def moduleMaurerCartanTargetForget (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) :
    (moduleHom R D M N).X q :=
  moduleHomElementMk R D q
    (fun x => maurerCartanTargetForgetCochain ((moduleHomπ R D N N x.unop).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x.unop)
      ((moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x.unop).f q z)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij) (moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [maurerCartanTargetForgetCochain, Cochain.mk_v, moduleMaurerCartan_map_v] using h)

lemma moduleMaurerCartanTargetRebase_π (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) (x : D) :
    (moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x).f q
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    maurerCartanTargetRebaseCochain ((moduleHomπ R D N N x).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x) ((moduleHomπ R D M N x).f q z) :=
  moduleHomElementMk_π R D q _ _ x

lemma moduleMaurerCartanTargetForget_π (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) (x : D) :
    (moduleHomπ R D M N x).f q (moduleMaurerCartanTargetForget R D N ψ hψ M q z) =
    maurerCartanTargetForgetCochain ((moduleHomπ R D N N x).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x)
      ((moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x).f q z) :=
  moduleHomElementMk_π R D q _ _ x

lemma moduleMaurerCartanTargetForget_rebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    moduleMaurerCartanTargetForget R D N ψ hψ M q
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) = z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetForget_π, moduleMaurerCartanTargetRebase_π]
  apply Cochain.ext
  intro i j hij
  rfl

lemma moduleMaurerCartanTargetRebase_forget (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) :
    moduleMaurerCartanTargetRebase R D N ψ hψ M q
      (moduleMaurerCartanTargetForget R D N ψ hψ M q z) = z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetRebase_π, moduleMaurerCartanTargetForget_π]
  apply Cochain.ext
  intro i j hij
  rfl


def moduleMaurerCartanTargetHomEquiv (M : RightModule R D) (q : ℤ) :
    (moduleHom R D M N).X q ≃ₗ[R]
      (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q where
  toFun := moduleMaurerCartanTargetRebase R D N ψ hψ M q
  invFun := moduleMaurerCartanTargetForget R D N ψ hψ M q
  left_inv := moduleMaurerCartanTargetForget_rebase R D N ψ hψ M q
  right_inv := moduleMaurerCartanTargetRebase_forget R D N ψ hψ M q
  map_add' z w := by
    apply moduleHomElement_ext R D
    intro x
    simp only [map_add, moduleMaurerCartanTargetRebase_π]
    apply Cochain.ext
    intro i j hij
    rfl
  map_smul' c z := by
    apply moduleHomElement_ext R D
    intro x
    simp only [map_smul, moduleMaurerCartanTargetRebase_π, RingHom.id_apply]
    apply Cochain.ext
    intro i j hij
    rfl

end SerrePositivity.DifferentialGraded

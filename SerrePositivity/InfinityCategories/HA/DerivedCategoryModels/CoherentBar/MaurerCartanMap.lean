module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：MC 作用素と可換な元の加群射を、両端の実 MC 加群の閉零射へ移す。
方針：元の全次数自然な零サイクルを成分を保って移し、既存の MC Hom 微分公式で閉性を示す。
規約：元の全 dg 作用を保持する。対象ごとに独立した鎖写像だけでは代用しない。
使われ方：同じ theta の bar から正規化 bar への実射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M N : ModuleCategory R D)
  (θ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) M)).X 1)
  (ψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N)).X 1)
  (hθ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) M)).d 1 2 θ +
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) M)
      θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N)).d 1 2 ψ +
    compose R (x := ForgetEnrichment.to (Complex R) N)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) N)
      ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (p : M ⟶ N)

def dgCoherentBarMaurerCartanMapElement :
    (moduleHom R D
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ)
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ)).X 0 :=
  moduleHomElementMk R D 0
    (fun x => Cochain.mk (fun i j hij =>
      ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) N) x.unop).f 0
        (closedHomEquiv R (RightModule R D) M N p).val).v i j hij)) (by
    intro x y q a
    have hmapM (i j : ℤ) (hij : i + q = j) :
        (((moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ).map x y).f q a).v
          i j hij = (((ForgetEnrichment.to (Complex R) M).map x y).f q a).v i j hij := rfl
    have hmapN (i j : ℤ) (hij : i + q = j) :
        (((moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ).map x y).f q a).v
          i j hij = (((ForgetEnrichment.to (Complex R) N).map x y).f q a).v i j hij := rfl
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (moduleHomElement_naturality R D
        (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) N) 0
        (closedHomEquiv R (RightModule R D) M N p).val x y q a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + q) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + 0) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, hmapM, hmapN] using h)

lemma dgCoherentBarMaurerCartanMapElement_closed
    (hp : (eHomWhiskerRight (Complex R) p N).f 1 ψ =
      (eHomWhiskerLeft (Complex R) M p).f 1 θ) :
    (moduleHom R D
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ)
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ)).d 0 1
      (dgCoherentBarMaurerCartanMapElement R D M N θ ψ hθ hψ p) = 0 := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomElement_d_π, map_zero]
  let θx := (moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) M) x).f 1 θ
  let ψx := (moduleHomπ R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N) x).f 1 ψ
  have hθx := moduleMaurerCartan_evaluation R D _ θ hθ x
  have hψx := moduleMaurerCartan_evaluation R D _ ψ hψ x
  let z := (closedHomEquiv R (RightModule R D) M N p).val
  let zx := (moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N) x).f 0 z
  have hrebase : (moduleHomπ R D
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ)
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ) x).f 0
      (dgCoherentBarMaurerCartanMapElement R D M N θ ψ hθ hψ p) =
      maurerCartanRebaseCochain θx ψx hθx hψx zx := by
    rw [dgCoherentBarMaurerCartanMapElement, moduleHomElementMk_π]
    rfl
  rw [hrebase]
  apply (maurerCartanCochainEquiv θx ψx hθx hψx 1).symm.injective
  change maurerCartanForgetCochain θx ψx hθx hψx
    (δ 0 1 (maurerCartanRebaseCochain θx ψx hθx hψx zx)) = 0
  have hδ := maurerCartanHom_δ θx ψx hθx hψx 0 zx
  change maurerCartanForgetCochain θx ψx hθx hψx
    (δ 0 1 (maurerCartanRebaseCochain θx ψx hθx hψx zx)) =
    δ 0 1 zx + zx.comp ψx (show (0 : ℤ) + 1 = 1 from rfl) +
      (1 : ℤ).negOnePow • θx.comp zx (show (1 : ℤ) + 0 = 1 from rfl) at hδ
  rw [hδ]
  have hz : δ 0 1 zx = 0 := by
    have hc := (closedHomEquiv R (RightModule R D) M N p).property
    change (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).d 0 1 z = 0 at hc
    have hd := moduleHomElement_d_π R D
      (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) N)
      0 1 z x
    rw [hc, map_zero] at hd
    exact hd.symm
  have hc := congrArg (fun f => (moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N) x).f 1 f) hp
  rw [moduleHomWhiskerRight_apply_π, moduleHomWhiskerLeft_apply_π] at hc
  have hpcycle : Cochain.ofHom ((moduleEvaluation R D x).map p) = zx :=
    moduleEvaluation_cochain R D x p
  rw [hpcycle] at hc
  rw [hz]
  change 0 + zx.comp ψx (by omega) + (1 : ℤ).negOnePow •
    θx.comp zx (by omega) = 0
  rw [hc]
  dsimp only [θx]
  simp only [zero_add, Int.negOnePow_one, Units.smul_def, Units.val_neg,
    Units.val_one, neg_one_zsmul, add_neg_cancel]

def dgCoherentBarMaurerCartanMap
    (hp : (eHomWhiskerRight (Complex R) p N).f 1 ψ =
      (eHomWhiskerLeft (Complex R) M p).f 1 θ) :
    ForgetEnrichment.of (Complex R)
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ) ⟶
    ForgetEnrichment.of (Complex R)
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ) :=
  moduleMorphismOfCycle R D (dgCoherentBarMaurerCartanMapElement R D M N θ ψ hθ hψ p)
    (dgCoherentBarMaurerCartanMapElement_closed R D M N θ ψ hθ hψ p hp)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

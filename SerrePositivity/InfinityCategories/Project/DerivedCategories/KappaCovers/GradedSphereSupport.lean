module
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.ActionLimits

/-!
概要：自由 sphere からの任意次数の主 Hom 要素は、直和内で有限 support を持つ。
方針：全 Hom end の自由評価と single 複体の生成元評価を線形同値として合成する。
規約：閉性を要求せず全次数で成立する。使われ方：semifree cell の微分の依存ラベル抽出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgKappaFreeSphereHomElementEquiv (x : D) (n p : ℤ) (M : ModuleCategory R D) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (freeSphere R D x n))
      (ForgetEnrichment.to (Complex R) M)).X p ≃ₗ[R]
      ((moduleEvaluation R D x).obj M).X (n + p) :=
  (((HomologicalComplex.eval (ModuleCat R) (.up ℤ) p).mapIso
    (freeHomIso R D x (complexSphere R n) (ForgetEnrichment.to (Complex R) M))).toLinearEquiv).trans
    (complexSphereHomElementLinearEquiv R ((moduleEvaluation R D x).obj M) n p)

lemma dgKappaSphereHomElement_postcompose {K L : Complex R} (g : K ⟶ L)
    (n p : ℤ) (a : (homComplex R (complexSphere R n) K).X p) :
    complexSphereHomElementEquiv R L n p ((homPostcompose (complexSphere R n) g).f p a) =
      g.f (n + p) (complexSphereHomElementEquiv R K n p a) := by
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat R))).inv ≫
    (a.comp (Cochain.ofHom g) (add_zero p)).v n (n + p) rfl) (1 : R) = _
  rw [Cochain.comp_v _ _ (add_zero p) n (n + p) (n + p) rfl (add_zero (n + p)), Cochain.ofHom_v]
  rfl

lemma dgKappaFreeSphereHomElement_natural (x : D) (n p : ℤ)
    {M N : ModuleCategory R D} (g : M ⟶ N)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) (freeSphere R D x n))
      (ForgetEnrichment.to (Complex R) M)).X p) :
    dgKappaFreeSphereHomElementEquiv R D x n p N
      ((eHomWhiskerLeft (Complex R) (freeSphere R D x n) g).f p a) =
      ((moduleEvaluation R D x).map g).f (n + p) (dgKappaFreeSphereHomElementEquiv R D x n p M a) := by
  have h := congrArg (fun k => k.f p a)
    (freeHomIso_naturality_target R D x (complexSphere R n) g)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  have hh := congrArg (complexSphereHomElementEquiv R ((moduleEvaluation R D x).obj N) n p) h
  have hp := dgKappaSphereHomElement_postcompose R ((moduleEvaluation R D x).map g) n p
    ((freeHomIso R D x (complexSphere R n) (ForgetEnrichment.to (Complex R) M)).hom.f p a)
  simpa only [dgKappaFreeSphereHomElementEquiv, LinearEquiv.trans_apply,
    CategoryTheory.Iso.toLinearEquiv_apply, CategoryTheory.Functor.mapIso_hom,
    complexSphereHomElementLinearEquiv] using! hh.trans hp

lemma dgKappaFreeSphereHomElement_coproduct_rep {J : Type u} (x : D) (n p : ℤ)
    (M : J → ModuleCategory R D)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) (freeSphere R D x n))
      (ForgetEnrichment.to (Complex R) (∐ M))).X p) :
    ∃ (t : Finset J) (b : ∀ j, (moduleHom R D
      (ForgetEnrichment.to (Complex R) (freeSphere R D x n))
      (ForgetEnrichment.to (Complex R) (M j))).X p),
      ∑ j ∈ t, (eHomWhiskerLeft (Complex R) (freeSphere R D x n) (Sigma.ι M j)).f p (b j) = a := by
  classical
  let E := moduleEvaluation R D x
  let c : Cofan (fun j => E.obj (M j)) := Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hc : IsColimit c := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, z, hz⟩ := complexCofan_element_rep R (fun j => E.obj (M j)) c hc (n + p)
    (dgKappaFreeSphereHomElementEquiv R D x n p (∐ M) a)
  let b := fun j => (dgKappaFreeSphereHomElementEquiv R D x n p (M j)).symm (z j)
  refine ⟨t, b, ?_⟩
  apply (dgKappaFreeSphereHomElementEquiv R D x n p (∐ M)).injective
  simpa only [map_sum, dgKappaFreeSphereHomElement_natural, b, c, E,
    LinearEquiv.apply_symm_apply] using! hz

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers

module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanRestriction

/-!
概要：同じ θ と可換する内部鎖写像を、両側の MC 微分変更の射にする。
方針：各評価で元の全次数成分を保ち、加群の全斉次作用の自然性を戻す。
規約：元の dg 加群作用を変更しない。
使われ方：実 bar の段階包含と隣接層の射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Preadditive DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]

def cutPerturbComplexMap {K L : Complex R} (f : K ⟶ L)
    (θ : Cochain K K 1) (ψ : Cochain L L 1)
    (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
    (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
    (hf : (Cochain.ofHom f).comp ψ (zero_add 1) = θ.comp (Cochain.ofHom f) (add_zero 1)) :
    maurerCartanPerturbComplex K θ hθ ⟶ maurerCartanPerturbComplex L ψ hψ :=
  CochainComplex.ofHom (fun q => f.f q) (fun q => by
    rw [maurerCartanPerturbComplex_d, maurerCartanPerturbComplex_d,
      add_comp, comp_add, f.comm]
    congr 1
    have h := congrArg (fun z : Cochain K L 1 => z.v q (q + 1) rfl) hf
    simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v] using h)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M N : ModuleCategory R D}
  (θ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) M)).X 1)
  (ψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N)).X 1)
  (hθ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) M)).d 1 2 θ + compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) M) θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N)).d 1 2 ψ + compose R (x := ForgetEnrichment.to (Complex R) N)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) N) ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (f : M ⟶ N)
  (hf : (eHomWhiskerRight (Complex R) f N).f 1 ψ =
    (eHomWhiskerLeft (Complex R) M f).f 1 θ)

def cutPerturbModuleApp (x : Dᵒᵖ) :
    (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) M) θ hθ).obj x ⟶
      (moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) N) ψ hψ).obj x := by
  apply cutPerturbComplexMap ((moduleEvaluation R D x.unop).map f)
    ((moduleHomπ R D _ _ x.unop).f 1 θ) ((moduleHomπ R D _ _ x.unop).f 1 ψ)
    (moduleMaurerCartan_evaluation R D _ θ hθ x.unop)
    (moduleMaurerCartan_evaluation R D _ ψ hψ x.unop)
  have h := congrArg (fun z => (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) M) (ForgetEnrichment.to (Complex R) N) x.unop).f 1 z) hf
  simpa only [moduleHomWhiskerRight_apply_π, moduleHomWhiskerLeft_apply_π] using! h

def dgBarMaurerCartanModuleMap :
    ForgetEnrichment.of (Complex R) (moduleMaurerCartan R D
      (ForgetEnrichment.to (Complex R) M) θ hθ) ⟶
    ForgetEnrichment.of (Complex R) (moduleMaurerCartan R D
      (ForgetEnrichment.to (Complex R) N) ψ hψ) :=
  moduleMorphismMk R D (cutPerturbModuleApp R D θ ψ hθ hψ f hf) (fun x y => by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun g => (g.f p a).v i j hij)
      ((moduleMapFamilyEquiv R D M N f).property x y)
    simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homPostcompose_apply,
      homPrecompose_apply, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, moduleMaurerCartanMap_v] using! h)

@[simp]
lemma dgBarMaurerCartanModuleMap_eval_f (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgBarMaurerCartanModuleMap R D θ ψ hθ hψ f hf)).f q =
      ((moduleEvaluation R D x).map f).f q := by
  rw [dgBarMaurerCartanModuleMap, moduleMorphismMk_eval]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

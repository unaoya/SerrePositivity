module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomDegrees
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits Preadditive DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

def dgCoherentBarEndRebase (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).X q :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D _ _ x.unop).f q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule_map_v] using h)

lemma dgCoherentBarEndRebase_π (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q) (x : D)
    (i j : ℤ) (hij : i + q = j) :
    ((moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) x).f q
      (dgCoherentBarEndRebase R D F hMC q z)).v i j hij =
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D _ _ x).f q z).v i j hij := by
  rw [dgCoherentBarEndRebase, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
  rfl

lemma dgCoherentBarEndRebase_add (q : ℤ)
    (z w : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q) :
    dgCoherentBarEndRebase R D F hMC q (z + w) =
      dgCoherentBarEndRebase R D F hMC q z + dgCoherentBarEndRebase R D F hMC q w := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  simp only [map_add, dgCoherentBarEndRebase, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
  apply Cochain.ext
  intro i j hij
  rfl

lemma dgCoherentBarEndRebase_d (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)).d q (q + 1)
      (dgCoherentBarEndRebase R D F hMC q z) =
    dgCoherentBarEndRebase R D F hMC (q + 1)
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d q (q + 1) z +
        compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) z rfl +
        (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
          (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
          z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (by omega : 1 + q = q + 1)) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  let M := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
  let θ := (moduleHomπ R D M M x).f 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
  have hθ := moduleMaurerCartan_evaluation R D M (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) hMC x
  have hrebase (p : ℤ) (w : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M M).X p) :
      (moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) x).f p (dgCoherentBarEndRebase R D F hMC p w) =
      _root_.SerrePositivity.DifferentialGraded.maurerCartanRebaseCochain θ θ hθ hθ ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D M M x).f p w) := by
    apply Cochain.ext
    intro i j hij
    rw [dgCoherentBarEndRebase_π]
    rfl
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π, hrebase, hrebase]
  apply (_root_.SerrePositivity.DifferentialGraded.maurerCartanCochainEquiv θ θ hθ hθ (q + 1)).symm.injective
  change _root_.SerrePositivity.DifferentialGraded.maurerCartanForgetCochain θ θ hθ hθ
    (δ q (q + 1) (_root_.SerrePositivity.DifferentialGraded.maurerCartanRebaseCochain θ θ hθ hθ
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D M M x).f q z))) = _
  rw [_root_.SerrePositivity.DifferentialGraded.maurerCartanHom_δ]
  change _ = (_root_.SerrePositivity.DifferentialGraded.maurerCartanCochainEquiv θ θ hθ hθ (q + 1)).symm
    ((_root_.SerrePositivity.DifferentialGraded.maurerCartanCochainEquiv θ θ hθ hθ (q + 1)) _)
  rw [LinearEquiv.symm_apply_apply]
  dsimp only [M, θ]
  rw [← _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π R D q (q + 1) z x,
    ← moduleHomCompose_π R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) z rfl x,
    ← moduleHomCompose_π R D z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
      (by omega : 1 + q = q + 1) x]
  have hadd {A B : ModuleCat.{u} R} (f : A ⟶ B) (a b c : A) (k : ℤˣ) :
      f (a + b + k • c) = f a + f b + k • f c := by
    change f.hom (a + b + k • c) = f.hom a + f.hom b + k • f.hom c
    simp only [map_add, Units.smul_def, map_zsmul]
  exact (hadd ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D M M x).f (q + 1)) _ _ _ (q + 1).negOnePow).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

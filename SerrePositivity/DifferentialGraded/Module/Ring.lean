module
public import SerrePositivity.DifferentialGraded.Module.Category

/-! # 一対象 dg 環 A の右加群と非有界複体 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A]

/-- 任意パラメータの射に対する豊穣左単位の公式。 -/
lemma identity_tensor_comp {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (identity P ⊗ₘ f) ≫ enrichedComposition P P Q = (λ_ K).hom ≫ f := by
  apply (cancel_epi (λ_ K).inv).1
  rw [leftUnitor_inv_comp_tensorHom_assoc, identity_comp]
  simp

/-- 任意パラメータの射に対する豊穣右単位の公式。 -/
lemma tensor_identity_comp {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (f ⊗ₘ identity Q) ≫ enrichedComposition P Q Q = (ρ_ K).hom ≫ f := by
  apply (cancel_epi (ρ_ K).inv).1
  rw [rightUnitor_inv_comp_tensorHom_assoc, comp_identity]
  simp

/-- A のみが作用する一対象加群の全次数自然性。 -/
lemma ringParamNaturality {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (β_ K (𝟙_ (Complex A))).hom ≫ (identity P ⊗ₘ f) ≫ enrichedComposition P P Q =
      (f ⊗ₘ identity Q) ≫ enrichedComposition P Q Q := by
  rw [identity_tensor_comp, tensor_identity_comp, ← Category.assoc, braiding_leftUnitor]

/-- 複体 P の一対象 A 上の右 dg 加群。作用は閉単位の chain map。 -/
abbrev ringModule (P : Complex A) : RightModule A PUnit.{1} where
  obj _ := P
  map _ _ := identity P
  map_id _ := by
    change 𝟙 _ ≫ identity P = identity P
    simp
  map_comp _ _ _ := by
    change ((β_ (𝟙_ (Complex A)) (𝟙_ (Complex A))).hom ≫
      (λ_ (𝟙_ (Complex A))).hom) ≫ identity P =
      (identity P ⊗ₘ identity P) ≫ enrichedComposition P P P
    rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id, Category.id_comp]
    simpa only [unitors_equal] using (identity_tensor_comp A (identity P)).symm

/-- 一対象右加群の作用は単位保存から一意に定まる。 -/
lemma ringModule_map (M : RightModule A PUnit.{1}) (x : PUnit.{1}ᵒᵖ) :
    M.map x x = identity (M.obj x) := by
  have h := M.toFunctor.map_id x
  change 𝟙 _ ≫ M.map x x = identity (M.obj x) at h
  simpa only [Category.id_comp] using h

/-- 一対象加群は唯一の対象での値から復元される。 -/
lemma ringModule_recover (M : RightModule A PUnit.{1}) :
    ringModule A (M.obj (op PUnit.unit)) = M := by
  rcases M with ⟨obj, map, hid, hcomp⟩
  obtain ⟨P, hp⟩ : ∃ P : Complex A, obj = fun _ => P := by
    refine ⟨obj (op PUnit.unit), ?_⟩
    funext x
    exact congrArg obj (Subsingleton.elim x (op PUnit.unit))
  subst obj
  have hm : map = fun _ _ => identity P := by
    funext x y
    have hxy : y = x := Subsingleton.elim y x
    subst y
    have h := hid x
    change 𝟙 _ ≫ map x x = identity P at h
    simpa only [Category.id_comp] using h
  subst map
  rfl

/-- 一対象環の加群対象と既存非有界複体の厳密な同値。 -/
def ringModuleObjEquiv : RightModule A PUnit.{1} ≃ Complex A where
  toFun M := M.obj (op PUnit.unit)
  invFun := ringModule A
  left_inv := ringModule_recover A
  right_inv _ := rfl

/-- 定数一対象加群の Hom end は通常の線形 Hom 複体。 -/
def ringConstantHomIso (P Q : Complex A) :
    moduleHom A PUnit.{1} (ringModule A P) (ringModule A Q) ≅ homComplex A P Q where
  hom := moduleHomπ A PUnit.{1} (ringModule A P) (ringModule A Q) PUnit.unit
  inv := (moduleHomEquiv A PUnit.{1} _ (ringModule A P) (ringModule A Q)).symm
    { app _ := 𝟙 _
      naturality _ _ := ringParamNaturality A (𝟙 _) }
  hom_inv_id := by
    apply moduleHom_ext
    intro x
    cases x
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
  inv_hom_id := by
    rw [moduleHomEquiv_symm_π]
    rfl

/-- 任意の一対象加群でも end 評価は chain iso。 -/
instance ringModuleHomπ_isIso (M N : RightModule A PUnit.{1}) :
    IsIso (moduleHomπ A PUnit.{1} M N PUnit.unit) := by
  rw [← ringModule_recover A M, ← ringModule_recover A N]
  exact Iso.isIso_hom (ringConstantHomIso A _ _)

/-- 一対象加群の全次数 Hom end と通常の Hom 複体の比較。 -/
abbrev ringModuleHomIso (M N : RightModule A PUnit.{1}) :
    moduleHom A PUnit.{1} M N ≅
      homComplex A (M.obj (op PUnit.unit)) (N.obj (op PUnit.unit)) :=
  asIso (moduleHomπ A PUnit.{1} M N PUnit.unit)

/-- 一対象加群の閉零射と通常の chain map の同値。 -/
def ringEvaluationHomEquiv (M N : ModuleCategory A PUnit.{1}) :
    (M ⟶ N) ≃ ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M ⟶
      (moduleEvaluation A PUnit.{1} PUnit.unit).obj N) :=
  (Iso.homCongr (Iso.refl (𝟙_ (Complex A)))
    (ringModuleHomIso A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N))).trans (complexClosedHomEquiv A _ _)

/-- 一対象評価の射は上の Hom 同値で計算される。 -/
lemma ringEvaluation_map {M N : ModuleCategory A PUnit.{1}} (f : M ⟶ N) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map f = ringEvaluationHomEquiv A M N f := by
  rfl

/-- 一対象環での評価は充満。 -/
instance ringEvaluation_full : (moduleEvaluation A PUnit.{1} PUnit.unit).Full where
  map_surjective {M N} := by
    rw [funext (fun f => ringEvaluation_map A f)]
    exact (ringEvaluationHomEquiv A M N).surjective

/-- 一対象環での評価は忠実。 -/
instance ringEvaluation_faithful : (moduleEvaluation A PUnit.{1} PUnit.unit).Faithful where
  map_injective := by
    intro M N f g h
    rw [ringEvaluation_map, ringEvaluation_map] at h
    exact (ringEvaluationHomEquiv A M N).injective h

/-- 一対象環での評価は全複体を与える。 -/
instance ringEvaluation_essSurj : (moduleEvaluation A PUnit.{1} PUnit.unit).EssSurj where
  mem_essImage P := ⟨ForgetEnrichment.of (Complex A) (ringModule A P), ⟨Iso.refl P⟩⟩

/-- 充満・忠実・本質的全射による評価の同値性。 -/
instance ringEvaluation_isEquivalence :
    (moduleEvaluation A PUnit.{1} PUnit.unit).IsEquivalence where

/-- 一対象 dg 環 A 上の右加群の閉零圏は通常の非有界複体圏と同値。 -/
def ringModuleEquivalence : ModuleCategory A PUnit.{1} ≌ Complex A :=
  (moduleEvaluation A PUnit.{1} PUnit.unit).asEquivalence
end SerrePositivity.DifferentialGraded

module
public import SerrePositivity.DifferentialGraded.Module.ActionChain
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # dg 加群の objectwise 極限

まず各評価図式の極限存在を明示して全次数作用を構成する。
大きい添字圏について存在を暗黙に仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCategory A D)
variable [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)]

/-- 各対象での既存複体の極限。 -/
abbrev moduleLimitValue (x : Dᵒᵖ) : Complex A := limit (F ⋙ moduleEvaluation A D x.unop)

/-- Hom tensor と始域の極限から、終域の評価図式への作用 cone。 -/
def moduleLimitActionCone (x y : Dᵒᵖ) : Cone (F ⋙ moduleEvaluation A D y.unop) where
  pt := (x ⟶[Complex A] y) ⊗ moduleLimitValue A D F x
  π.app j := (𝟙 (x ⟶[Complex A] y) ⊗ₘ limit.π (F ⋙ moduleEvaluation A D x.unop) j) ≫
    moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y
  π.naturality {j k} f := by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    symm
    change ((𝟙 (x ⟶[Complex A] y) ⊗ₘ limit.π (F ⋙ moduleEvaluation A D x.unop) j) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y) ≫
        (moduleEvaluation A D y.unop).map (F.map f) = _
    rw [Category.assoc, moduleMorphism_action_chain,
      ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    have hw := limit.w (F := F ⋙ moduleEvaluation A D x.unop) f
    simp only [Functor.comp_map] at hw
    exact congrArg (fun t : moduleLimitValue A D F x ⟶
      (moduleEvaluation A D x.unop).obj (F.obj k) =>
        (𝟙 (x ⟶[Complex A] y) ⊗ₘ t) ≫
          moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj k)) x y) hw

/-- 極限の値に作用する全次数 tensor chain map。 -/
def moduleLimitAction (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⊗ moduleLimitValue A D F x ⟶ moduleLimitValue A D F y :=
  limit.lift (F ⋙ moduleEvaluation A D y.unop) (moduleLimitActionCone A D F x y)

/-- 作用を極限の射影で評価すると、元の加群作用になる。 -/
@[reassoc]
lemma moduleLimitAction_π (x y : Dᵒᵖ) (j : J) :
    moduleLimitAction A D F x y ≫ limit.π (F ⋙ moduleEvaluation A D y.unop) j =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ limit.π (F ⋙ moduleEvaluation A D x.unop) j) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y :=
  limit.lift_π _ _

/-- 極限上の全次数 Hom chain map。 -/
def moduleLimitHom (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⟶ homComplex A (moduleLimitValue A D F x) (moduleLimitValue A D F y) :=
  curryRight (moduleLimitAction A D F x y)

/-- 全次数 Hom と極限射影の可換式。 -/
lemma moduleLimitHom_π (x y : Dᵒᵖ) (j : J) :
    moduleLimitHom A D F x y ≫ homPostcompose (moduleLimitValue A D F x)
      (limit.π (F ⋙ moduleEvaluation A D y.unop) j) =
    (ForgetEnrichment.to (Complex A) (F.obj j)).map x y ≫
      homPrecompose (limit.π (F ⋙ moduleEvaluation A D x.unop) j)
        ((ForgetEnrichment.to (Complex A) (F.obj j)).obj y) := by
  unfold moduleLimitHom
  rw [← curryRight_naturality_target]
  rw [moduleLimitAction_π, curryRight_naturality_domain, curryRight_uncurryRight]
  rfl
/-- 極限射影と全斉次作用の可換式。 -/
lemma moduleLimitHom_π_v (x y : Dᵒᵖ) (j : J) (p i n : ℤ) (hn : i + p = n)
    (f : GradedHom A x y p) :
    ((moduleLimitHom A D F x y).f p f).v i n hn ≫
      (limit.π (F ⋙ moduleEvaluation A D y.unop) j).f n =
    (limit.π (F ⋙ moduleEvaluation A D x.unop) j).f i ≫
      (((ForgetEnrichment.to (Complex A) (F.obj j)).map x y).f p f).v i n hn := by
  have h := congrArg (fun l => l.f p f) (moduleLimitHom_π A D F x y j)
  change ((moduleLimitHom A D F x y).f p f).comp
      (Cochain.ofHom (limit.π (F ⋙ moduleEvaluation A D y.unop) j)) (add_zero p) =
    (Cochain.ofHom (limit.π (F ⋙ moduleEvaluation A D x.unop) j)).comp
      (((ForgetEnrichment.to (Complex A) (F.obj j)).map x y).f p f) (zero_add p) at h
  have hv := Cochain.congr_v h i n hn
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v] using hv

/-- 極限 Hom 作用は単位を保存する。 -/
lemma moduleLimitHom_id (x : Dᵒᵖ) :
    eId (Complex A) x ≫ moduleLimitHom A D F x x = identity (moduleLimitValue A D F x) := by
  apply homComplex_limit_ext (F ⋙ moduleEvaluation A D x.unop)
  intro j
  rw [Category.assoc, moduleLimitHom_π, ← Category.assoc]
  rw [(ForgetEnrichment.to (Complex A) (F.obj j)).toFunctor.map_id]
  exact (identity_hom_naturality (limit.π (F ⋙ moduleEvaluation A D x.unop) j)).symm

/-- 極限 Hom 作用は全次数の豊穣合成を保存する。 -/
lemma moduleLimitHom_comp (x y z : Dᵒᵖ) :
    eComp (Complex A) x y z ≫ moduleLimitHom A D F x z =
      (moduleLimitHom A D F x y ⊗ₘ moduleLimitHom A D F y z) ≫
        enrichedComposition _ _ _ := by
  apply homComplex_limit_ext (F ⋙ moduleEvaluation A D z.unop)
  intro j
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change ((moduleLimitHom A D F x z).f n (forward A f g hn)).comp
      (Cochain.ofHom (limit.π (F ⋙ moduleEvaluation A D z.unop) j)) (add_zero n) =
    ((enrichedComposition _ _ _).f n
      ((moduleLimitHom A D F x y ⊗ₘ moduleLimitHom A D F y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))).comp
          (Cochain.ofHom (limit.π (F ⋙ moduleEvaluation A D z.unop) j)) (add_zero n)
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i l hil
  rw [Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Cochain.units_smul_v,
    Cochain.comp_v _ _ hn i (i + p) l rfl (by omega)]
  rw [moduleLimitHom_π_v]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [moduleLimitHom_π_v]
  rw [← Category.assoc, moduleLimitHom_π_v]
  rw [moduleMap_forward, Cochain.units_smul_v,
    Cochain.comp_v _ _ hn i (i + p) l rfl (by omega)]
  simp only [Linear.comp_units_smul, Category.assoc]

/-- objectwise 複体極限に全次数作用を与えた右 dg 加群。 -/
abbrev limitModule : RightModule A D where
  obj := moduleLimitValue A D F
  map := moduleLimitHom A D F
  map_id := moduleLimitHom_id A D F
  map_comp := moduleLimitHom_comp A D F
/-- 主閉零加群圏に置いた具体的 objectwise 極限対象。 -/
abbrev moduleLimitObj : ModuleCategory A D := ForgetEnrichment.of (Complex A) (limitModule A D F)

/-- 極限の射影は全次数自然な閉零加群射。 -/
def moduleLimitπ (j : J) : moduleLimitObj A D F ⟶ F.obj j :=
  moduleMorphismMk A D (M := limitModule A D F)
    (N := ForgetEnrichment.to (Complex A) (F.obj j))
    (fun x => limit.π (F ⋙ moduleEvaluation A D x.unop) j)
    (fun x y => moduleLimitHom_π A D F x y j)

@[simp] lemma moduleLimitπ_eval (j : J) (x : D) :
    (moduleEvaluation A D x).map (moduleLimitπ A D F j) =
      limit.π (F ⋙ moduleEvaluation A D x) j := moduleMorphismMk_eval A D _ _ x

/-- 全次数自然な射影からなる加群圏の cone。 -/
def moduleLimitCone : Cone F where
  pt := moduleLimitObj A D F
  π.app := moduleLimitπ A D F
  π.naturality {j k} f := by
    change 𝟙 _ ≫ moduleLimitπ A D F k = moduleLimitπ A D F j ≫ F.map f
    rw [Category.id_comp]
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleLimitπ_eval]
    exact (limit.w (F := F ⋙ moduleEvaluation A D x) f).symm

/-- 任意の加群 cone の objectwise lift。 -/
def moduleLimitLiftValue (s : Cone F) (x : Dᵒᵖ) :
    (ForgetEnrichment.to (Complex A) s.pt).obj x ⟶ moduleLimitValue A D F x :=
  limit.lift (F ⋙ moduleEvaluation A D x.unop) ((moduleEvaluation A D x.unop).mapCone s)

@[reassoc] lemma moduleLimitLiftValue_π (s : Cone F) (x : Dᵒᵖ) (j : J) :
    moduleLimitLiftValue A D F s x ≫ limit.π (F ⋙ moduleEvaluation A D x.unop) j =
      (moduleEvaluation A D x.unop).map (s.π.app j) := limit.lift_π _ _

/-- objectwise lift は全次数 tensor 作用と可換。 -/
lemma moduleLimitLiftValue_action (s : Cone F) (x y : Dᵒᵖ) :
    moduleActionChain A (ForgetEnrichment.to (Complex A) s.pt) x y ≫
      moduleLimitLiftValue A D F s y =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ moduleLimitLiftValue A D F s x) ≫
      moduleLimitAction A D F x y := by
  apply limit.hom_ext
  intro j
  rw [Category.assoc, moduleLimitLiftValue_π, Category.assoc, moduleLimitAction_π]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, moduleLimitLiftValue_π]
  exact moduleMorphism_action_chain A D (s.π.app j) x y

/-- objectwise lift は Hom 複体の全次数自然性を満たす。 -/
lemma moduleLimitLiftValue_naturality (s : Cone F) (x y : Dᵒᵖ) :
    (ForgetEnrichment.to (Complex A) s.pt).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) s.pt).obj x)
        (moduleLimitLiftValue A D F s y) =
    moduleLimitHom A D F x y ≫ homPrecompose (moduleLimitLiftValue A D F s x)
      (moduleLimitValue A D F y) := by
  have h := congrArg curryRight (moduleLimitLiftValue_action A D F s x y)
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight] at h
  exact h

/-- 普遍 lift を主 Hom end の閉零射へ持ち上げる。 -/
def moduleLimitLift (s : Cone F) : s.pt ⟶ moduleLimitObj A D F :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) s.pt)
    (N := limitModule A D F) (moduleLimitLiftValue A D F s)
    (moduleLimitLiftValue_naturality A D F s)

@[simp] lemma moduleLimitLift_eval (s : Cone F) (x : D) :
    (moduleEvaluation A D x).map (moduleLimitLift A D F s) =
      moduleLimitLiftValue A D F s (op x) := moduleMorphismMk_eval A D _ _ x

/-- objectwise 極限 cone は加群圏の真の極限。 -/
def moduleLimitConeIsLimit : IsLimit (moduleLimitCone A D F) where
  lift := moduleLimitLift A D F
  fac s j := by
    change moduleLimitLift A D F s ≫ moduleLimitπ A D F j = s.π.app j
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleLimitLift_eval, moduleLimitπ_eval]
    exact moduleLimitLiftValue_π A D F s (op x) j
  uniq s m hm := by
    apply moduleMorphism_ext
    intro x
    rw [moduleLimitLift_eval]
    apply limit.hom_ext
    intro j
    have hh : m ≫ moduleLimitπ A D F j = s.π.app j := hm j
    have h := congrArg (fun t => (moduleEvaluation A D x).map t) hh
    simp only [CategoryTheory.Functor.map_comp, moduleLimitπ_eval] at h
    rw [moduleLimitLiftValue_π]
    exact h
/-- 各評価の極限存在から加群図式の極限存在を得る。 -/
lemma moduleHasLimit_of_evaluations : HasLimit F :=
  HasLimit.mk ⟨moduleLimitCone A D F, moduleLimitConeIsLimit A D F⟩

/-- 構成した加群極限 cone の評価は既存の極限 cone に同型。 -/
def moduleLimitConeEvaluationIso (x : D) :
    limit.cone (F ⋙ moduleEvaluation A D x) ≅
      (moduleEvaluation A D x).mapCone (moduleLimitCone A D F) :=
  Cone.ext (Iso.refl _) (by
    intro j
    symm
    change 𝟙 _ ≫ (moduleEvaluation A D x).map (moduleLimitπ A D F j) =
      limit.π (F ⋙ moduleEvaluation A D x) j
    rw [Category.id_comp, moduleLimitπ_eval])

/-- 評価した極限 cone は既存複体圏で極限。 -/
def moduleLimitConeEvaluationIsLimit (x : D) :
    IsLimit ((moduleEvaluation A D x).mapCone (moduleLimitCone A D F)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (moduleLimitConeEvaluationIso A D F x)

/-- 各評価関手は存在する objectwise 極限を保存する。 -/
instance moduleEvaluationPreservesLimit (x : D) : PreservesLimit F (moduleEvaluation A D x) :=
  preservesLimit_of_preserves_limit_cone (moduleLimitConeIsLimit A D F)
    (moduleLimitConeEvaluationIsLimit A D F x)

/-- 選ばれた加群極限の評価と既存複体の極限の標準比較。 -/
def moduleEvaluationLimitIso [HasLimit F] (x : D) :
    (moduleEvaluation A D x).obj (limit F) ≅ limit (F ⋙ moduleEvaluation A D x) :=
  preservesLimitIso (moduleEvaluation A D x) F

@[reassoc] lemma moduleEvaluationLimitIso_hom_π [HasLimit F] (x : D) (j : J) :
    (moduleEvaluationLimitIso A D F x).hom ≫ limit.π (F ⋙ moduleEvaluation A D x) j =
      (moduleEvaluation A D x).map (limit.π F j) := preservesLimitIso_hom_π _ _ j

omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- u-small な添字対象族の図式の極限。射の宇宙 w' は独立。 -/
instance moduleHasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (ModuleCategory A D) where
  has_limit G := by
    let : HasLimitsOfShape J (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
    let : HasLimitsOfShape J (Complex A) := inferInstance
    exact moduleHasLimit_of_evaluations A D G

omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 評価関手は u-small な全添字図式の極限を保存する。 -/
instance moduleEvaluationPreservesLimitsOfShape [Small.{u} J] (x : D) :
    PreservesLimitsOfShape J (moduleEvaluation A D x) where
  preservesLimit {G} := by
    let : HasLimitsOfShape J (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
    let : HasLimitsOfShape J (Complex A) := inferInstance
    exact moduleEvaluationPreservesLimit A D G x

omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 添字対象宇宙 u、添字射宇宙 w' の全極限。 -/
instance moduleHasLimitsOfSize : HasLimitsOfSize.{w', u} (ModuleCategory A D) where

omit [∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 評価は添字対象宇宙 u の全極限を保存する。 -/
instance moduleEvaluationPreservesLimitsOfSize (x : D) :
    PreservesLimitsOfSize.{w', u} (moduleEvaluation A D x) where
end SerrePositivity.DifferentialGraded

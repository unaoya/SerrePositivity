module

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Module.ActionLimits

## 概要
3 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ActionChain（旧 SerrePositivity/DifferentialGraded/Module/ActionChain.lean） -/

/-! # 全次数作用を tensor の chain map として読む -/

@[expose] public section ActionChain
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全次数の右作用の符号なし転置。 -/
abbrev moduleActionChain (M : RightModule A D) (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⊗ M.obj x ⟶ M.obj y := uncurryRight (M.map x y)

/-- 全次数自然な chain map 族は tensor 作用の chain map と可換。 -/
lemma closedFamily_action_chain {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    moduleActionChain A M x y ≫ a y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ a x) ≫ moduleActionChain A N x y := by
  apply (tensorRightHomEquiv (M.obj x) (x ⟶[Complex A] y) (N.obj y)).injective
  change curryRight (uncurryRight (M.map x y) ≫ a y) =
    curryRight ((𝟙 (x ⟶[Complex A] y) ⊗ₘ a x) ≫ uncurryRight (N.map x y))
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h x y

variable (D) [Small.{u} D]
/-- 加群圏の実際の射は全次数 tensor 作用と可換。 -/
lemma moduleMorphism_action_chain {M N : ModuleCategory A D} (f : M ⟶ N) (x y : Dᵒᵖ) :
    moduleActionChain A (ForgetEnrichment.to (Complex A) M) x y ≫
      (moduleEvaluation A D y.unop).map f =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ (moduleEvaluation A D x.unop).map f) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) N) x y :=
  closedFamily_action_chain A (closedTransApp A (moduleClosedHomEquiv A D M N f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)) x y
end SerrePositivity.DifferentialGraded
end

end ActionChain

/-! ## Limits（旧 SerrePositivity/DifferentialGraded/Module/Limits.lean） -/

/-! # dg 加群の objectwise 極限

まず各評価図式の極限存在を明示して全次数作用を構成する。
大きい添字圏について存在を暗黙に仮定しない。
-/

@[expose] public section Limits
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end Limits

/-! ## Colimits（旧 SerrePositivity/DifferentialGraded/Module/Colimits.lean） -/

/-! # dg 加群の objectwise 余極限

全次数 tensor 作用は、閉構造による左 tensor の余極限保存から構成する。
大きい図式には各評価の余極限存在を明示する。
-/

@[expose] public section Colimits
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCategory A D)
variable [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)]

/-- 各対象での既存複体の余極限。 -/
abbrev moduleColimitValue (x : Dᵒᵖ) : Complex A := colimit (F ⋙ moduleEvaluation A D x.unop)

/-- Hom tensor を施した評価図式から、終域の余極限への作用 cocone。 -/
def moduleColimitActionCocone (x y : Dᵒᵖ) :
    Cocone ((F ⋙ moduleEvaluation A D x.unop) ⋙ tensorLeft (x ⟶[Complex A] y)) where
  pt := moduleColimitValue A D F y
  ι.app j := moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y ≫
    colimit.ι (F ⋙ moduleEvaluation A D y.unop) j
  ι.naturality {j k} f := by
    change ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (F.map f)) ≫
      (moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj k)) x y ≫
        colimit.ι (F ⋙ moduleEvaluation A D y.unop) k) = _ ≫ 𝟙 _
    rw [Category.comp_id, ← id_tensorHom, ← Category.assoc, ← moduleMorphism_action_chain]
    have hw := colimit.w (F := F ⋙ moduleEvaluation A D y.unop) f
    simp only [Functor.comp_map] at hw
    rw [Category.assoc]
    exact congrArg (fun t : (moduleEvaluation A D y.unop).obj (F.obj j) ⟶
      moduleColimitValue A D F y =>
        moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y ≫ t) hw

/-- 余極限の値への全次数 tensor 作用。 -/
def moduleColimitAction (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⊗ moduleColimitValue A D F x ⟶ moduleColimitValue A D F y :=
  (isColimitOfPreserves (tensorLeft (x ⟶[Complex A] y))
    (colimit.isColimit (F ⋙ moduleEvaluation A D x.unop))).desc
      (moduleColimitActionCocone A D F x y)

/-- 余極限包含前の作用は元の加群作用。 -/
@[reassoc] lemma moduleColimitAction_ι (x y : Dᵒᵖ) (j : J) :
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ colimit.ι (F ⋙ moduleEvaluation A D x.unop) j) ≫
      moduleColimitAction A D F x y =
    moduleActionChain A (ForgetEnrichment.to (Complex A) (F.obj j)) x y ≫
      colimit.ι (F ⋙ moduleEvaluation A D y.unop) j := by
  rw [id_tensorHom]
  exact (isColimitOfPreserves (tensorLeft (x ⟶[Complex A] y))
    (colimit.isColimit (F ⋙ moduleEvaluation A D x.unop))).fac
      (moduleColimitActionCocone A D F x y) j

/-- 余極限上の全次数 Hom chain map。 -/
def moduleColimitHom (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⟶ homComplex A (moduleColimitValue A D F x) (moduleColimitValue A D F y) :=
  curryRight (moduleColimitAction A D F x y)

/-- 全次数 Hom と余極限包含の可換式。 -/
lemma moduleColimitHom_ι (x y : Dᵒᵖ) (j : J) :
    moduleColimitHom A D F x y ≫ homPrecompose (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)
      (moduleColimitValue A D F y) =
    (ForgetEnrichment.to (Complex A) (F.obj j)).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) (F.obj j)).obj x)
        (colimit.ι (F ⋙ moduleEvaluation A D y.unop) j) := by
  unfold moduleColimitHom
  rw [← curryRight_naturality_domain, moduleColimitAction_ι,
    curryRight_naturality_target, curryRight_uncurryRight]
  rfl
/-- 余極限包含と全斉次作用の可換式。 -/
lemma moduleColimitHom_ι_v (x y : Dᵒᵖ) (j : J) (p i n : ℤ) (hn : i + p = n)
    (f : GradedHom A x y p) :
    (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j).f i ≫
      ((moduleColimitHom A D F x y).f p f).v i n hn =
    (((ForgetEnrichment.to (Complex A) (F.obj j)).map x y).f p f).v i n hn ≫
      (colimit.ι (F ⋙ moduleEvaluation A D y.unop) j).f n := by
  have h := congrArg (fun l => l.f p f) (moduleColimitHom_ι A D F x y j)
  change (Cochain.ofHom (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)).comp
      ((moduleColimitHom A D F x y).f p f) (zero_add p) =
    (((ForgetEnrichment.to (Complex A) (F.obj j)).map x y).f p f).comp
      (Cochain.ofHom (colimit.ι (F ⋙ moduleEvaluation A D y.unop) j)) (add_zero p) at h
  have hv := Cochain.congr_v h i n hn
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v] using hv

/-- 余極限 Hom 作用は単位を保存する。 -/
lemma moduleColimitHom_id (x : Dᵒᵖ) :
    eId (Complex A) x ≫ moduleColimitHom A D F x x = identity (moduleColimitValue A D F x) := by
  apply homComplex_colimit_ext (F ⋙ moduleEvaluation A D x.unop)
  intro j
  rw [Category.assoc, moduleColimitHom_ι, ← Category.assoc]
  rw [(ForgetEnrichment.to (Complex A) (F.obj j)).toFunctor.map_id]
  exact identity_hom_naturality (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)

/-- 余極限 Hom 作用は全次数の豊穣合成を保存する。 -/
lemma moduleColimitHom_comp (x y z : Dᵒᵖ) :
    eComp (Complex A) x y z ≫ moduleColimitHom A D F x z =
      (moduleColimitHom A D F x y ⊗ₘ moduleColimitHom A D F y z) ≫
        enrichedComposition _ _ _ := by
  apply homComplex_colimit_ext (F ⋙ moduleEvaluation A D x.unop)
  intro j
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (Cochain.ofHom (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)).comp
      ((moduleColimitHom A D F x z).f n (forward A f g hn)) (zero_add n) =
    (Cochain.ofHom (colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)).comp
      ((enrichedComposition _ _ _).f n
        ((moduleColimitHom A D F x y ⊗ₘ moduleColimitHom A D F y z).f n
          (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g))))
      (zero_add n)
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i l hil
  rw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.units_smul_v, Cochain.comp_v _ _ hn i (i + p) l rfl (by omega)]
  rw [moduleColimitHom_ι_v]
  simp only [Linear.comp_units_smul, ← Category.assoc]
  rw [moduleColimitHom_ι_v]
  rw [Category.assoc, moduleColimitHom_ι_v]
  rw [moduleMap_forward, Cochain.units_smul_v,
    Cochain.comp_v _ _ hn i (i + p) l rfl (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc]

/-- objectwise 複体余極限に全次数作用を与えた右 dg 加群。 -/
abbrev colimitModule : RightModule A D where
  obj := moduleColimitValue A D F
  map := moduleColimitHom A D F
  map_id := moduleColimitHom_id A D F
  map_comp := moduleColimitHom_comp A D F
/-- 主閉零加群圏に置いた具体的 objectwise 余極限対象。 -/
abbrev moduleColimitObj : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (colimitModule A D F)

/-- 余極限の包含は全次数自然な閉零加群射。 -/
def moduleColimitι (j : J) : F.obj j ⟶ moduleColimitObj A D F :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (F.obj j))
    (N := colimitModule A D F)
    (fun x => colimit.ι (F ⋙ moduleEvaluation A D x.unop) j)
    (fun x y => (moduleColimitHom_ι A D F x y j).symm)

@[simp] lemma moduleColimitι_eval (j : J) (x : D) :
    (moduleEvaluation A D x).map (moduleColimitι A D F j) =
      colimit.ι (F ⋙ moduleEvaluation A D x) j := moduleMorphismMk_eval A D _ _ x

/-- 全次数自然な包含からなる加群圏の cocone。 -/
def moduleColimitCocone : Cocone F where
  pt := moduleColimitObj A D F
  ι.app := moduleColimitι A D F
  ι.naturality {j k} f := by
    change F.map f ≫ moduleColimitι A D F k = moduleColimitι A D F j ≫ 𝟙 _
    rw [Category.comp_id]
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleColimitι_eval]
    exact colimit.w (F := F ⋙ moduleEvaluation A D x) f

/-- 任意の加群 cocone への objectwise desc。 -/
def moduleColimitDescValue (s : Cocone F) (x : Dᵒᵖ) :
    moduleColimitValue A D F x ⟶ (ForgetEnrichment.to (Complex A) s.pt).obj x :=
  colimit.desc (F ⋙ moduleEvaluation A D x.unop) ((moduleEvaluation A D x.unop).mapCocone s)

@[reassoc] lemma moduleColimitDescValue_ι (s : Cocone F) (x : Dᵒᵖ) (j : J) :
    colimit.ι (F ⋙ moduleEvaluation A D x.unop) j ≫ moduleColimitDescValue A D F s x =
      (moduleEvaluation A D x.unop).map (s.ι.app j) := colimit.ι_desc _ _

/-- objectwise desc は全次数 tensor 作用と可換。 -/
lemma moduleColimitDescValue_action (s : Cocone F) (x y : Dᵒᵖ) :
    moduleColimitAction A D F x y ≫ moduleColimitDescValue A D F s y =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ moduleColimitDescValue A D F s x) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) s.pt) x y := by
  apply (isColimitOfPreserves (tensorLeft (x ⟶[Complex A] y))
    (colimit.isColimit (F ⋙ moduleEvaluation A D x.unop))).hom_ext
  intro j
  change ((x ⟶[Complex A] y) ◁ colimit.ι (F ⋙ moduleEvaluation A D x.unop) j) ≫
      (moduleColimitAction A D F x y ≫ moduleColimitDescValue A D F s y) =
    ((x ⟶[Complex A] y) ◁ colimit.ι (F ⋙ moduleEvaluation A D x.unop) j) ≫
      ((𝟙 (x ⟶[Complex A] y) ⊗ₘ moduleColimitDescValue A D F s x) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A) s.pt) x y)
  rw [← id_tensorHom, ← Category.assoc, moduleColimitAction_ι, Category.assoc,
    moduleColimitDescValue_ι]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, moduleColimitDescValue_ι]
  exact moduleMorphism_action_chain A D (s.ι.app j) x y

/-- objectwise desc は Hom 複体の全次数自然性を満たす。 -/
lemma moduleColimitDescValue_naturality (s : Cocone F) (x y : Dᵒᵖ) :
    moduleColimitHom A D F x y ≫ homPostcompose (moduleColimitValue A D F x)
      (moduleColimitDescValue A D F s y) =
    (ForgetEnrichment.to (Complex A) s.pt).map x y ≫
      homPrecompose (moduleColimitDescValue A D F s x)
        ((ForgetEnrichment.to (Complex A) s.pt).obj y) := by
  have h := congrArg curryRight (moduleColimitDescValue_action A D F s x y)
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight] at h
  exact h

/-- 普遍 desc を主 Hom end の閉零射へ持ち上げる。 -/
def moduleColimitDesc (s : Cocone F) : moduleColimitObj A D F ⟶ s.pt :=
  moduleMorphismMk A D (M := colimitModule A D F)
    (N := ForgetEnrichment.to (Complex A) s.pt) (moduleColimitDescValue A D F s)
    (moduleColimitDescValue_naturality A D F s)

@[simp] lemma moduleColimitDesc_eval (s : Cocone F) (x : D) :
    (moduleEvaluation A D x).map (moduleColimitDesc A D F s) =
      moduleColimitDescValue A D F s (op x) := moduleMorphismMk_eval A D _ _ x

/-- objectwise 余極限 cocone は加群圏の真の余極限。 -/
def moduleColimitCoconeIsColimit : IsColimit (moduleColimitCocone A D F) where
  desc := moduleColimitDesc A D F
  fac s j := by
    change moduleColimitι A D F j ≫ moduleColimitDesc A D F s = s.ι.app j
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleColimitDesc_eval, moduleColimitι_eval]
    exact moduleColimitDescValue_ι A D F s (op x) j
  uniq s m hm := by
    apply moduleMorphism_ext
    intro x
    rw [moduleColimitDesc_eval]
    apply colimit.hom_ext
    intro j
    have hh : moduleColimitι A D F j ≫ m = s.ι.app j := hm j
    have h := congrArg (fun t => (moduleEvaluation A D x).map t) hh
    simp only [CategoryTheory.Functor.map_comp, moduleColimitι_eval] at h
    rw [moduleColimitDescValue_ι]
    exact h
/-- 各評価の余極限存在から加群図式の余極限存在を得る。 -/
lemma moduleHasColimit_of_evaluations : HasColimit F :=
  HasColimit.mk ⟨moduleColimitCocone A D F, moduleColimitCoconeIsColimit A D F⟩

/-- 構成した加群余極限 cocone の評価は既存 cocone に同型。 -/
def moduleColimitCoconeEvaluationIso (x : D) :
    colimit.cocone (F ⋙ moduleEvaluation A D x) ≅
      (moduleEvaluation A D x).mapCocone (moduleColimitCocone A D F) :=
  Cocone.ext (Iso.refl _) (by
    intro j
    change colimit.ι (F ⋙ moduleEvaluation A D x) j ≫ 𝟙 _ =
      (moduleEvaluation A D x).map (moduleColimitι A D F j)
    rw [Category.comp_id, moduleColimitι_eval])

/-- 評価した余極限 cocone は既存複体圏で余極限。 -/
def moduleColimitCoconeEvaluationIsColimit (x : D) :
    IsColimit ((moduleEvaluation A D x).mapCocone (moduleColimitCocone A D F)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (moduleColimitCoconeEvaluationIso A D F x)

/-- 各評価関手は存在する objectwise 余極限を保存する。 -/
instance moduleEvaluationPreservesColimit (x : D) : PreservesColimit F (moduleEvaluation A D x) :=
  preservesColimit_of_preserves_colimit_cocone (moduleColimitCoconeIsColimit A D F)
    (moduleColimitCoconeEvaluationIsColimit A D F x)

/-- 選ばれた加群余極限の評価と既存複体余極限の標準比較。 -/
def moduleEvaluationColimitIso [HasColimit F] (x : D) :
    (moduleEvaluation A D x).obj (colimit F) ≅ colimit (F ⋙ moduleEvaluation A D x) :=
  preservesColimitIso (moduleEvaluation A D x) F

@[reassoc] lemma moduleEvaluationColimitIso_ι_hom [HasColimit F] (x : D) (j : J) :
    (moduleEvaluation A D x).map (colimit.ι F j) ≫ (moduleEvaluationColimitIso A D F x).hom =
      colimit.ι (F ⋙ moduleEvaluation A D x) j := ι_preservesColimitIso_hom _ _ j

omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- u-small な添字対象族の図式の余極限。射の宇宙 w' は独立。 -/
instance moduleHasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (ModuleCategory A D) where
  has_colimit G := by
    let : HasColimitsOfShape J (ModuleCat.{u} A) := inferInstance
    let : HasColimitsOfShape J (Complex A) := inferInstance
    exact moduleHasColimit_of_evaluations A D G

omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 評価関手は u-small な全添字図式の余極限を保存する。 -/
instance moduleEvaluationPreservesColimitsOfShape [Small.{u} J] (x : D) :
    PreservesColimitsOfShape J (moduleEvaluation A D x) where
  preservesColimit {G} := by
    let : HasColimitsOfShape J (ModuleCat.{u} A) := inferInstance
    let : HasColimitsOfShape J (Complex A) := inferInstance
    exact moduleEvaluationPreservesColimit A D G x

omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 添字対象宇宙 u、添字射宇宙 w' の全余極限。 -/
instance moduleHasColimitsOfSize : HasColimitsOfSize.{w', u} (ModuleCategory A D) where

omit [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] in
/-- 評価は添字対象宇宙 u の全余極限を保存する。 -/
instance moduleEvaluationPreservesColimitsOfSize (x : D) :
    PreservesColimitsOfSize.{w', u} (moduleEvaluation A D x) where
end SerrePositivity.DifferentialGraded
end

end Colimits

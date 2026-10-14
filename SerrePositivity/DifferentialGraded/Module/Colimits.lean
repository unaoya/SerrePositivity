module
public import SerrePositivity.DifferentialGraded.Module.Limits
public import SerrePositivity.DifferentialGraded.Complexes.HomColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # dg 加群の objectwise 余極限

全次数 tensor 作用は、閉構造による左 tensor の余極限保存から構成する。
大きい図式には各評価の余極限存在を明示する。
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

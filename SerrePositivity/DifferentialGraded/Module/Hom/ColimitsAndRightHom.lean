module

public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
# Module.Hom.ColimitsAndRightHom

## 概要
余極限・制限の Hom 比較と右 Hom 加群をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## EvaluationReflects（旧 SerrePositivity/DifferentialGraded/Module/EvaluationReflects.lean） -/

/-! # 評価による主dg加群圏の同型・余極限の反映 -/

@[expose] public section EvaluationReflects
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各評価が同型である主加群射は同型。逆射も全dg自然。 -/
lemma moduleIsIso_of_evaluations {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : ∀ x : D, IsIso ((moduleEvaluation A D x).map f)) : IsIso f := by
  let (x : D) : IsIso ((moduleEvaluation A D x).map f) := hf x
  let e : M ≅ N := moduleIsoMk A D
    (fun x : Dᵒᵖ => asIso ((moduleEvaluation A D x.unop).map f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f))
  have he : e.hom = f := by
    apply moduleMorphism_ext
    intro x
    exact moduleIsoMk_hom_eval A D _ _ x
  rw [← he]
  infer_instance

/-- 各評価の余極限が存在する図式について、全評価の余極限性を反映する。 -/
def moduleIsColimitOfEvaluations {J : Type w} [Category.{w'} J]
    {F : J ⥤ ModuleCategory A D}
    [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] (c : Cocone F)
    (hc : ∀ x : D, IsColimit ((moduleEvaluation A D x).mapCocone c)) : IsColimit c := by
  let : IsIso (moduleColimitDesc A D F c) :=
    moduleIsIso_of_evaluations A D (moduleColimitDesc A D F c) (by
      intro x
      rw [moduleColimitDesc_eval]
      exact inferInstanceAs (IsIso
        ((colimit.isColimit (F ⋙ moduleEvaluation A D x)).coconePointUniqueUpToIso (hc x)).hom))
  let e : moduleColimitCocone A D F ≅ c :=
    Cocone.ext (asIso (moduleColimitDesc A D F c))
      (fun j => (moduleColimitCoconeIsColimit A D F).fac c j)
  exact IsColimit.ofIsoColimit (moduleColimitCoconeIsColimit A D F) e

end SerrePositivity.DifferentialGraded
end

end EvaluationReflects

/-! ## TensorSource（旧 SerrePositivity/DifferentialGraded/Module/TensorSource.lean） -/

/-! # 固定複体とのtensorの加群変数での関手性と余極限保存 -/

@[expose] public section TensorSource
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma tensorModuleFamilyMap_naturality (K : Complex A) {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (tensorModule K M).map x y ≫ homPostcompose (K ⊗ M.obj x) (𝟙 K ⊗ₘ a y) =
      (tensorModule K N).map x y ≫ homPrecompose (𝟙 K ⊗ₘ a x) (K ⊗ N.obj y) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((tensorModule K M).map x y).f p f).comp
      (Cochain.ofHom (𝟙 K ⊗ₘ a y)) (add_zero p) =
    (Cochain.ofHom (𝟙 K ⊗ₘ a x)).comp
      (((tensorModule K N).map x y).f p f) (zero_add p)
  apply Cochain.ext
  intro r n hr
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = r at hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t v
  change (𝟙 K ⊗ₘ a y).f n (moduleAction A (tensorModule K M) f
      (ιTensorObj K (M.obj x) i j r hij (t ⊗ₜ[A] v)) hr) =
    moduleAction A (tensorModule K N) f
      ((𝟙 K ⊗ₘ a x).f r (ιTensorObj K (M.obj x) i j r hij (t ⊗ₜ[A] v))) hr
  rw [tensorModule_action K M x y p i j r (j + p) n hij rfl hr, tensorMap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorMap_apply, tensorModule_action K N x y p i j r (j + p) n hij rfl hr]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  exact congrArg (fun z => (p * i).negOnePow.val •
    ιTensorObj K (N.obj y) i (j + p) n (by omega) (t ⊗ₜ[A] z))
      (closedFamily_action A a h x y p j (j + p) rfl f v)

abbrev moduleTensorLeftObj (K : Complex A) (M : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (tensorModule K (ForgetEnrichment.to (Complex A) M))

def moduleTensorLeftMap (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleTensorLeftObj A D K M ⟶ moduleTensorLeftObj A D K N :=
  moduleMorphismMk A D (fun x => 𝟙 K ⊗ₘ closedTransApp A (moduleClosedHomEquiv A D M N f) x)
    (tensorModuleFamilyMap_naturality A D K _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

@[simp] lemma moduleTensorLeftMap_eval (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleTensorLeftMap A D K f) =
      𝟙 K ⊗ₘ (moduleEvaluation A D x).map f :=
  moduleMorphismMk_eval A D _ _ x

@[implicit_reducible]
def moduleTensorLeftFunctor (K : Complex A) : ModuleCategory A D ⥤ ModuleCategory A D where
  obj := moduleTensorLeftObj A D K
  map := moduleTensorLeftMap A D K
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleTensorLeftMap_eval, CategoryTheory.Functor.map_id,
      tensorHom_id, id_whiskerRight, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleTensorLeftMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, moduleTensorLeftMap_eval, moduleTensorLeftMap_eval]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- 評価と左tensorの可換比較。 -/
def moduleTensorLeftEvaluationIso (K : Complex A) (x : D) :
    moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A D x ⋙ tensorLeft K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (moduleEvaluation A D x).map (moduleTensorLeftMap A D K f) ≫ 𝟙 _ =
      𝟙 _ ≫ K ◁ (moduleEvaluation A D x).map f
    rw [moduleTensorLeftMap_eval, Category.comp_id, Category.id_comp, id_tensorHom])

instance moduleTensorLeftPreservesColimit (K : Complex A) {J : Type w} [Category.{w'} J]
    [Small.{u} J] (F : J ⥤ ModuleCategory A D) :
    PreservesColimit F (moduleTensorLeftFunctor A D K) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply moduleIsColimitOfEvaluations A D
  intro x
  let : PreservesColimit F (moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x) :=
    preservesColimit_of_natIso F (moduleTensorLeftEvaluationIso A D K x).symm
  exact isColimitOfPreserves (moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x)
    (colimit.isColimit F)

end SerrePositivity.DifferentialGraded
end

end TensorSource

/-! ## ParamCurry（旧 SerrePositivity/DifferentialGraded/Module/ParamCurry.lean） -/

/-! # パラメータ付きHom endの転置と加群変数の自然性 -/

@[expose] public section ParamCurry
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tensor加群からの射を主Hom endへのchain mapへ転置する。 -/
def moduleParamCurry {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) :
    K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) :=
  (moduleHomEquiv A D K _ _).symm
    (tensorFamilyCurry A (K := K) (M := ForgetEnrichment.to (Complex A) M)
      (N := ForgetEnrichment.to (Complex A) N)
      (closedTransApp A (moduleClosedHomEquiv A D (moduleTensorLeftObj A D K M) N f))
      (closedTransApp_naturality A
        (moduleClosedHomEquiv A D (moduleTensorLeftObj A D K M) N f)))

@[reassoc] lemma moduleParamCurry_π {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) (x : D) :
    moduleParamCurry A D f ≫
        moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x =
      curryRight ((moduleEvaluation A D x).map f) := by
  unfold moduleParamCurry
  rw [moduleHomEquiv_symm_π]
  rfl

@[simp] lemma moduleParamUncurry_curry {K : Complex A} {M N : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) :
    moduleParamUncurry A D (moduleParamCurry A D f) = f := by
  apply moduleMorphism_ext
  intro x
  rw [moduleParamUncurry_eval, moduleParamCurry_π, uncurryRight_curryRight]

@[simp] lemma moduleParamCurry_uncurry {K : Complex A} {M N : ModuleCategory A D}
    (a : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)) :
    moduleParamCurry A D (moduleParamUncurry A D a) = a := by
  apply moduleHom_ext
  intro x
  rw [moduleParamCurry_π, moduleParamUncurry_eval, curryRight_uncurryRight]
  simp only [ForgetEnrichment.to_of]

lemma moduleParamUncurry_injective {K : Complex A} {M N : ModuleCategory A D}
    {a b : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)}
    (h : moduleParamUncurry A D a = moduleParamUncurry A D b) : a = b := by
  have hh := congrArg (moduleParamCurry A D) h
  simpa only [moduleParamCurry_uncurry] using hh

/-- 加群変数への前合成と逆転置の整合性。 -/
lemma moduleParamUncurry_naturality_source {K : Complex A} {M P N : ModuleCategory A D}
    (f : M ⟶ P) (a : K ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)) :
    moduleTensorLeftMap A D K f ≫ moduleParamUncurry A D a =
      moduleParamUncurry A D (a ≫ eHomWhiskerRight (Complex A) f N) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleTensorLeftMap_eval,
    moduleParamUncurry_eval, moduleParamUncurry_eval]
  have hπ := congrArg (fun b => a ≫ b) (moduleHomWhiskerRight_π A D f x (P := N))
  rw [← Category.assoc] at hπ
  change (𝟙 K ⊗ₘ (moduleEvaluation A D x).map f) ≫
    uncurryRight (a ≫ moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N) x) =
    uncurryRight ((a ≫ eHomWhiskerRight (Complex A) f N) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x)
  refine Eq.trans ?_ (congrArg uncurryRight hπ.symm)
  apply (tensorRightHomEquiv _ _ _).injective
  change curryRight ((𝟙 K ⊗ₘ (moduleEvaluation A D x).map f) ≫ uncurryRight _) =
    curryRight (uncurryRight _)
  rw [curryRight_naturality_domain, curryRight_uncurryRight, curryRight_uncurryRight,
    Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded
end

end ParamCurry

/-! ## ColimitHom（旧 SerrePositivity/DifferentialGraded/Module/ColimitHom.lean） -/

/-! # 余極限を源とする主Hom endの極限表示 -/

@[expose] public section ColimitHom
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] [Small.{u} J]

abbrev moduleHomSourceDiagram (F : J ⥤ ModuleCategory A D) (N : ModuleCategory A D) :
    Jᵒᵖ ⥤ Complex A :=
  F.op ⋙ (eHomFunctor (Complex A) (ModuleCategory A D)).flip.obj N

def moduleColimitHomCone {F : J ⥤ ModuleCategory A D} (c : Cocone F)
    (N : ModuleCategory A D) : Cone (moduleHomSourceDiagram A D F N) where
  pt := moduleHom A D (ForgetEnrichment.to (Complex A) c.pt)
    (ForgetEnrichment.to (Complex A) N)
  π :=
    { app := fun j => eHomWhiskerRight (Complex A) (c.ι.app j.unop) N
      naturality := by
        intro i j f
        dsimp
        rw [Category.id_comp]
        change eHomWhiskerRight (Complex A) (c.ι.app j.unop) N =
          eHomWhiskerRight (Complex A) (c.ι.app i.unop) N ≫
            eHomWhiskerRight (Complex A) (F.map f.unop) N
        rw [← eHomWhiskerRight_comp, c.w f.unop] }

def moduleColimitHomUncurryCocone {F : J ⥤ ModuleCategory A D}
    (N : ModuleCategory A D) (s : Cone (moduleHomSourceDiagram A D F N)) :
    Cocone (F ⋙ moduleTensorLeftFunctor A D s.pt) where
  pt := N
  ι :=
    { app := fun j => moduleParamUncurry A D (s.π.app (op j))
      naturality := by
        intro i j f
        dsimp
        rw [Category.comp_id]
        exact (moduleParamUncurry_naturality_source A D (F.map f) (s.π.app (op j))).trans
          (congrArg (moduleParamUncurry A D) (s.w f.op)) }

def moduleColimitHomLift {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D)
    (s : Cone (moduleHomSourceDiagram A D F N)) :
    s.pt ⟶ (moduleColimitHomCone A D c N).pt :=
  moduleParamCurry A D ((isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
    (moduleColimitHomUncurryCocone A D N s))

lemma moduleColimitHomLift_π {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D)
    (s : Cone (moduleHomSourceDiagram A D F N)) (j : Jᵒᵖ) :
    moduleColimitHomLift A D hc N s ≫ eHomWhiskerRight (Complex A) (c.ι.app j.unop) N =
      s.π.app j := by
  apply moduleParamUncurry_injective A D (M := F.obj j.unop) (N := N)
  have hn := moduleParamUncurry_naturality_source A D (c.ι.app j.unop)
    (moduleColimitHomLift A D hc N s)
  have hu : moduleParamUncurry A D (moduleColimitHomLift A D hc N s) =
      (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
        (moduleColimitHomUncurryCocone A D N s) := moduleParamUncurry_curry A D _
  have hf : moduleTensorLeftMap A D s.pt (c.ι.app j.unop) ≫
      (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
        (moduleColimitHomUncurryCocone A D N s) = moduleParamUncurry A D (s.π.app j) :=
    (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).fac _ j.unop
  exact hn.symm.trans
    ((congrArg (fun b => moduleTensorLeftMap A D s.pt (c.ι.app j.unop) ≫ b) hu).trans hf)

def moduleColimitHomIsLimit {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D) :
    IsLimit (moduleColimitHomCone A D c N) where
  lift := moduleColimitHomLift A D hc N
  fac := moduleColimitHomLift_π A D hc N
  uniq s a ha := by
    apply moduleParamUncurry_injective A D (M := c.pt) (N := N)
    unfold moduleColimitHomLift
    rw [moduleParamUncurry_curry]
    apply (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).hom_ext
    intro j
    have hn := moduleParamUncurry_naturality_source A D (c.ι.app j)
      (show s.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) c.pt)
        (ForgetEnrichment.to (Complex A) N) from a)
    have hj : a ≫ eHomWhiskerRight (Complex A) (c.ι.app j) N = s.π.app (op j) := ha (op j)
    exact (hn.trans (congrArg (moduleParamUncurry A D) hj)).trans
      ((isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).fac
        (moduleColimitHomUncurryCocone A D N s) j).symm

end SerrePositivity.DifferentialGraded
end

end ColimitHom

/-! ## CoproductHom（旧 SerrePositivity/DifferentialGraded/Module/CoproductHom.lean） -/

/-! # 余積を源とする全次数Hom endの直積表示 -/

@[expose] public section CoproductHom
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

abbrev moduleCoproductHomFamily (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    J → Complex A :=
  fun j => moduleHom A D (ForgetEnrichment.to (Complex A) (M j)) (ForgetEnrichment.to (Complex A) N)

def moduleCoproductHomFan (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    Fan (moduleCoproductHomFamily A D M N) :=
  Fan.mk (moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M)) (ForgetEnrichment.to (Complex A) N))
    (fun j => eHomWhiskerRight (Complex A) (Sigma.ι M j) N)

/-- tensorの余積保存と各成分の逆転置によるHomへのlift。 -/
def moduleCoproductHomLift (M : J → ModuleCategory A D) (N : ModuleCategory A D)
    (c : Fan (moduleCoproductHomFamily A D M N)) :
    c.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M))
      (ForgetEnrichment.to (Complex A) N) :=
  moduleParamCurry A D
    (Cofan.IsColimit.desc
      (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
      (fun j => moduleParamUncurry A D (c.proj j)))

lemma moduleCoproductHomLift_π (M : J → ModuleCategory A D) (N : ModuleCategory A D)
    (c : Fan (moduleCoproductHomFamily A D M N)) (j : J) :
    moduleCoproductHomLift A D M N c ≫ eHomWhiskerRight (Complex A) (Sigma.ι M j) N = c.proj j := by
  apply moduleParamUncurry_injective A D (M := M j) (N := N)
  have hn := moduleParamUncurry_naturality_source A D (Sigma.ι M j)
    (moduleCoproductHomLift A D M N c)
  have hu : moduleParamUncurry A D (moduleCoproductHomLift A D M N c) =
      Cofan.IsColimit.desc
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
        (fun t => moduleParamUncurry A D (c.proj t)) :=
    moduleParamUncurry_curry A D _
  have hf : moduleTensorLeftMap A D c.pt (Sigma.ι M j) ≫
      Cofan.IsColimit.desc
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
        (fun t => moduleParamUncurry A D (c.proj t)) = moduleParamUncurry A D (c.proj j) :=
    Cofan.IsColimit.fac
      (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M) _ j
  exact hn.symm.trans
    ((congrArg (fun b => moduleTensorLeftMap A D c.pt (Sigma.ι M j) ≫ b) hu).trans hf)

/-- Hom endの標準射影が、真の直積を与える。 -/
def moduleCoproductHomIsLimit (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    IsLimit (moduleCoproductHomFan A D M N) :=
  Fan.IsLimit.mk _ (moduleCoproductHomLift A D M N)
    (fun c j => moduleCoproductHomLift_π A D M N c j) (by
      intro c a ha
      apply moduleParamUncurry_injective A D (M := ∐ M) (N := N)
      unfold moduleCoproductHomLift
      rw [moduleParamUncurry_curry]
      apply Cofan.IsColimit.hom_ext
        (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
      intro j
      simp only [cofan_mk_inj]
      have hn := moduleParamUncurry_naturality_source A D (Sigma.ι M j)
        (show c.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M))
          (ForgetEnrichment.to (Complex A) N) from a)
      have hj : a ≫ eHomWhiskerRight (Complex A) (Sigma.ι M j) N = c.proj j := ha j
      exact (hn.trans (congrArg (moduleParamUncurry A D) hj)).trans
        (Cofan.IsColimit.fac
          (isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D c.pt) M)
          (fun t => moduleParamUncurry A D (c.proj t)) j).symm)


/-- 全次数dg自然性と微分を保つchain iso。 -/
def moduleCoproductHomIso (M : J → ModuleCategory A D) (N : ModuleCategory A D) :
    moduleHom A D (ForgetEnrichment.to (Complex A) (∐ M)) (ForgetEnrichment.to (Complex A) N) ≅
      ∏ᶜ moduleCoproductHomFamily A D M N :=
  IsLimit.conePointUniqueUpToIso (moduleCoproductHomIsLimit A D M N) (productIsProduct _)

@[reassoc] lemma moduleCoproductHomIso_hom_π (M : J → ModuleCategory A D)
    (N : ModuleCategory A D) (j : J) :
    (moduleCoproductHomIso A D M N).hom ≫ Pi.π (moduleCoproductHomFamily A D M N) j =
      eHomWhiskerRight (Complex A) (Sigma.ι M j) N :=
  IsLimit.conePointUniqueUpToIso_hom_comp (moduleCoproductHomIsLimit A D M N)
    (productIsProduct _) ⟨j⟩

end SerrePositivity.DifferentialGraded
end

end CoproductHom

/-! ## RestrictionTensor（旧 SerrePositivity/DifferentialGraded/Module/RestrictionTensor.lean） -/

/-! # 制限とtensor、およびtensor加群の括弧変更

## 概要
制限とtensor、およびtensor加群の括弧変更。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/CylinderKFlat.lean、Bimodule/
RestrictedFree.lean。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionTensor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

def tensorModuleAssociatorIso [Small.{u} D] (K L : Complex A) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule K (tensorModule L M)) ≅
      ForgetEnrichment.of (Complex A) (tensorModule (K ⊗ L) M) :=
  moduleIsoMk A D (M := tensorModule K (tensorModule L M)) (N := tensorModule (K ⊗ L) M)
    (fun x => (α_ K L (M.obj x)).symm) (by
      intro x y
      apply hom_naturality_of_apply
      intro p f
      exact associator_inv_cochain_right K L (M.obj x) (M.obj y) p ((M.map x y).f p f))

variable (E : Type w) [DGCategory A E]

lemma restrictModule_tensor (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (K : Complex A) (M : RightModule A E) :
    restrictModule A D E F (tensorModule K M) = tensorModule K (restrictModule A D E F M) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (restrictModule A D E F (tensorModule K M)).toFunctor)
    (G := (tensorModule K (restrictModule A D E F M)).toFunctor) (fun _ => rfl)
  intro x y
  change (F.map x y ≫ (M.map (F.obj x) (F.obj y) ≫ tensorLeftHom K _ _)) ≫ 𝟙 _ =
    (F.map x y ≫ M.map (F.obj x) (F.obj y)) ≫ tensorLeftHom K _ _
  rw [Category.comp_id, Category.assoc]

def moduleRestrictionTensorIso [Small.{u} D] [Small.{u} E]
    (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (K : Complex A) (M : ModuleCategory A E) :
    (moduleRestriction A D E F).obj (moduleTensorLeftObj A E K M) ≅
      moduleTensorLeftObj A D K ((moduleRestriction A D E F).obj M) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A))
    (restrictModule_tensor A D E F K (ForgetEnrichment.to (Complex A) M)))

end SerrePositivity.DifferentialGraded
end

end RestrictionTensor

/-! ## RestrictionColimits（旧 SerrePositivity/DifferentialGraded/Module/RestrictionColimits.lean） -/

/-! # dg加群の制限は対象ごとの余極限を保つ

## 概要
dg加群の制限は対象ごとの余極限を保つ。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RightRestriction.lean、Tensor/
RestrictionSemifree.lean。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionColimits
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

lemma moduleRestriction_comp_evaluation (x : D) :
    moduleRestriction A D E F ⋙ moduleEvaluation A D x =
      moduleEvaluation A E (F.obj (op x)).unop := by
  exact CategoryTheory.Functor.ext
    (F := moduleRestriction A D E F ⋙ moduleEvaluation A D x)
    (G := moduleEvaluation A E (F.obj (op x)).unop) (fun _ => rfl)
    (fun _ _ f => by
      change (moduleEvaluation A D x).map ((moduleRestriction A D E F).map f) =
        (moduleEvaluation A E (F.obj (op x)).unop).map f
      exact moduleRestriction_map_eval A D E F f x)

variable {J : Type z} [Category.{z'} J] [Small.{u} J]

/-- 評価の余極限保存と反映により、制限されたcoconeも余極限。 -/
def moduleRestrictionIsColimit {G : J ⥤ ModuleCategory A E} (c : Cocone G) (hc : IsColimit c) :
    IsColimit ((moduleRestriction A D E F).mapCocone c) := by
  apply moduleIsColimitOfEvaluations A D
  intro x
  change IsColimit ((moduleRestriction A D E F ⋙ moduleEvaluation A D x).mapCocone c)
  rw [moduleRestriction_comp_evaluation]
  exact isColimitOfPreserves (moduleEvaluation A E (F.obj (op x)).unop) hc

instance moduleRestrictionPreservesColimitsOfShape :
    PreservesColimitsOfShape J (moduleRestriction A D E F) where
  preservesColimit {G} :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit G)
      (moduleRestrictionIsColimit A D E F (colimit.cocone G) (colimit.isColimit G))

def moduleRestrictionColimitIso (G : J ⥤ ModuleCategory A E) :
    (moduleRestriction A D E F).obj (colimit G) ≅ colimit (G ⋙ moduleRestriction A D E F) :=
  preservesColimitIso (moduleRestriction A D E F) G

end SerrePositivity.DifferentialGraded
end

end RestrictionColimits

/-! ## RestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Module/RestrictionCoherence.lean） -/

/-! # dg加群制限の恒等・合成比較

## 概要
比較の評価成分は恒等chain mapで、全Hom自然性は豊穣関手の結合則から得る。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleRestrictionIdObjIso (M : ModuleCategory A D) :
    (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M ≅ M :=
  moduleIsoMk A D
    (M := restrictModule A D D (DGFunctor.id Dᵒᵖ) (ForgetEnrichment.to (Complex A) M))
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, Cochain.comp_id, Cochain.id_comp]
    change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y).f p f = _
    rw [Category.id_comp])

@[simp] lemma moduleRestrictionIdObjIso_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionIdObjIso A D M).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A D _ _ x

def moduleRestrictionIdIso : moduleRestriction A D D (DGFunctor.id Dᵒᵖ) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (F := moduleRestriction A D D (DGFunctor.id Dᵒᵖ)) (G := 𝟭 (ModuleCategory A D))
    (moduleRestrictionIdObjIso A D) (by
    intro M N f
    apply moduleMorphism_ext
    intro x
    simp only [Functor.id_map, Functor.map_comp, moduleRestrictionIdObjIso,
      moduleIsoMk_hom_eval, moduleRestriction_map_eval]
    rfl)

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (G : DGFunctor A Eᵒᵖ Tᵒᵖ)

def moduleRestrictionCompObjIso (M : ModuleCategory A T) :
    (moduleRestriction A D E F).obj ((moduleRestriction A E T G).obj M) ≅
      (moduleRestriction A D T (F.comp G)).obj M :=
  moduleIsoMk A D
    (M := restrictModule A D E F
      (restrictModule A E T G (ForgetEnrichment.to (Complex A) M)))
    (N := restrictModule A D T (F.comp G) (ForgetEnrichment.to (Complex A) M))
    (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, Cochain.comp_id, Cochain.id_comp]
    change (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫
      (ForgetEnrichment.to (Complex A) M).map (G.obj (F.obj x)) (G.obj (F.obj y)))).f p f =
      ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫
        (ForgetEnrichment.to (Complex A) M).map (G.obj (F.obj x)) (G.obj (F.obj y))).f p f
    rw [Category.assoc])

@[simp] lemma moduleRestrictionCompObjIso_hom_eval (M : ModuleCategory A T) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionCompObjIso A D E T F G M).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A D _ _ x

def moduleRestrictionCompIso :
    moduleRestriction A E T G ⋙ moduleRestriction A D E F ≅
      moduleRestriction A D T (F.comp G) :=
  NatIso.ofComponents
    (F := moduleRestriction A E T G ⋙ moduleRestriction A D E F)
    (G := moduleRestriction A D T (F.comp G))
    (moduleRestrictionCompObjIso A D E T F G) (by
    intro M N f
    apply moduleMorphism_ext
    intro x
    simp only [Functor.comp_map, Functor.map_comp,
      moduleRestrictionCompObjIso_hom_eval,
      moduleRestriction_map_eval]
    rfl)

end SerrePositivity.DifferentialGraded
end

end RestrictionCoherence

/-! ## RestrictionGradedSplit（旧 SerrePositivity/DifferentialGraded/Module/RestrictionGradedSplit.lean） -/

/-! # dg加群の制限は全斉次作用に関する分裂を保つ

## 概要
dg加群の制限は全斉次作用に関する分裂を保つ。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/RestrictionSemifree.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionGradedSplit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- section/retractionの微分との可換性を要求せず、元の全次数自然性を制限する。 -/
def ModuleGradedSplit.restrict {M N P : ModuleCategory A E} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A E f g) :
    ModuleGradedSplit A D ((moduleRestriction A D E F).map f)
      ((moduleRestriction A D E F).map g) where
  retraction x n := s.retraction (F.obj (op x)).unop n
  section_ x n := s.section_ (F.obj (op x)).unop n
  inclusion_retraction x n := by
    rw [moduleRestriction_map_eval]
    exact s.inclusion_retraction (F.obj (op x)).unop n
  section_projection x n := by
    rw [moduleRestriction_map_eval]
    exact s.section_projection (F.obj (op x)).unop n
  section_retraction x n := s.section_retraction (F.obj (op x)).unop n
  inclusion_projection := by
    rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection, moduleRestriction_map_zero]
  decomposition x n := by
    rw [moduleRestriction_map_eval, moduleRestriction_map_eval]
    exact s.decomposition (F.obj (op x)).unop n
  retraction_naturality x y p i j hij a :=
    s.retraction_naturality (F.obj (op x)).unop (F.obj (op y)).unop p i j hij
      ((F.map (op x) (op y)).f p a)
  section_naturality x y p i j hij a :=
    s.section_naturality (F.obj (op x)).unop (F.obj (op y)).unop p i j hij
      ((F.map (op x) (op y)).f p a)

end SerrePositivity.DifferentialGraded
end

end RestrictionGradedSplit

/-! ## HomotopyCoproduct（旧 SerrePositivity/DifferentialGraded/Module/HomotopyCoproduct.lean） -/

/-! # 余積からの加群ホモトピーの成分判定 -/

@[expose] public section HomotopyCoproduct
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleHomCycle_precompose {M N T : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ T) :
    (eHomWhiskerRight (Complex A) f T).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π, ← moduleEvaluation_cochain A D x g,
    ← moduleEvaluation_cochain A D x (f ≫ g), CategoryTheory.Functor.map_comp,
    Cochain.ofHom_comp]

private def productElement (F : J → Complex A) (n : ℤ) (z : ∀ j, (F j).X n) :
    (∏ᶜ F).X n :=
  (Fan.IsLimit.lift (complexProductDegreeIsLimit A F n)
    (fun j => moduleElementMap A _ (z j))) (1 : A)

private lemma productElement_π (F : J → Complex A) (n : ℤ) (z : ∀ j, (F j).X n) (j : J) :
    (Pi.π F j).f n (productElement A F n z) = z j := by
  have h := congrArg (fun a => a (1 : A))
    (Fan.IsLimit.fac (complexProductDegreeIsLimit A F n)
      (fun j => moduleElementMap A _ (z j)) j)
  change (Pi.π F j).f n (productElement A F n z) = (1 : A) • z j at h
  simpa only [one_smul] using h

private lemma productElement_ext (F : J → Complex A) (n : ℤ) (a b : (∏ᶜ F).X n)
    (h : ∀ j, (Pi.π F j).f n a = (Pi.π F j).f n b) : a = b := by
  have hm : moduleElementMap A _ a = moduleElementMap A _ b := by
    apply complexProductDegree_hom_ext A F n
    intro j
    apply (moduleElementEquiv A _).injective
    change (Pi.π F j).f n ((1 : A) • a) = (Pi.π F j).f n ((1 : A) • b)
    simpa only [one_smul] using h j
  exact (moduleElementEquiv A _).symm.injective hm

lemma moduleCoproduct_homotopy_of_components (M : J → ModuleCategory A D)
    {N : ModuleCategory A D} (f g : ∐ M ⟶ N)
    (h : ∀ j, Nonempty (ModuleHomotopy A D (Sigma.ι M j ≫ f) (Sigma.ι M j ≫ g))) :
    Nonempty (ModuleHomotopy A D f g) := by
  let F := moduleCoproductHomFamily A D M N
  let e := moduleCoproductHomIso A D M N
  let hj := fun j => Classical.choice (h j)
  let t := productElement A F (-1) (fun j => (hj j).val)
  let b := e.inv.f (-1) t
  have hb (j : J) : (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f (-1) b = (hj j).val := by
    have he := congrArg (fun a => a.f (-1)) (moduleCoproductHomIso_hom_π A D M N j)
    have hi := congrArg (fun a => a.f (-1)) e.inv_hom_id
    have ht : e.hom.f (-1) b = t := congrArg (fun a => a t) hi
    calc
      _ = (Pi.π F j).f (-1) (e.hom.f (-1) b) := (congrArg (fun a => a b) he).symm
      _ = (Pi.π F j).f (-1) t := congrArg ((Pi.π F j).f (-1)) ht
      _ = _ := productElement_π A F (-1) _ j
  refine ⟨⟨b, ?_⟩⟩
  let C := moduleHom A D (ForgetEnrichment.to (Complex A) (show ModuleCategory A D from ∐ M))
    (ForgetEnrichment.to (Complex A) N)
  let zf := (cycleFromUnit C (ForgetEnrichment.homTo (Complex A) f)).val
  let zg := (cycleFromUnit C (ForgetEnrichment.homTo (Complex A) g)).val
  change C.d (-1) 0 b = zf - zg
  have hi : Function.Injective (e.hom.f 0) := by
    intro a b hab
    have he := congrArg (fun a => a.f 0) e.hom_inv_id
    have ha := congrArg (fun k => k a) he
    have hb := congrArg (fun k => k b) he
    exact ha.symm.trans ((congrArg (e.inv.f 0) hab).trans hb)
  apply hi
  apply productElement_ext A F 0
  intro j
  have he := congrArg (fun a => a.f 0) (moduleCoproductHomIso_hom_π A D M N j)
  have he' (a : C.X 0) : (Pi.π F j).f 0 (e.hom.f 0 a) =
      (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f 0 a := congrArg (fun k => k a) he
  rw [he', he']
  have hc := congrArg (fun k => k b)
    ((eHomWhiskerRight (Complex A) (Sigma.ι M j) N).comm (-1) 0)
  change (F j).d (-1) 0
      ((eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f (-1) b) =
    (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f 0 (C.d (-1) 0 b) at hc
  have hd : (F j).d (-1) 0 (hj j).val =
      (cycleFromUnit (F j) (ForgetEnrichment.homTo (Complex A) (Sigma.ι M j ≫ f))).val -
        (cycleFromUnit (F j) (ForgetEnrichment.homTo (Complex A) (Sigma.ι M j ≫ g))).val :=
    (hj j).property
  rw [← hc, hb, hd, map_sub]
  exact congrArg₂ (fun a b => a - b)
    (moduleHomCycle_precompose A D (Sigma.ι M j) f).symm
    (moduleHomCycle_precompose A D (Sigma.ι M j) g).symm

end SerrePositivity.DifferentialGraded
end

end HomotopyCoproduct

/-! ## HomotopyCoproductUniversal（旧 SerrePositivity/DifferentialGraded/Module/HomotopyCoproductUniversal.lean） -/

/-! # K(D)のu-small余積と商関手による余積の保存 -/

@[expose] public section HomotopyCoproductUniversal
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleHomotopyCoproduct_hom_ext (M : J → ModuleCategory A D)
    {N : ModuleHomotopyCategory A D}
    {f g : (moduleToHomotopy A D).obj (∐ M) ⟶ N}
    (h : ∀ j, (moduleToHomotopy A D).map (Sigma.ι M j) ≫ f =
      (moduleToHomotopy A D).map (Sigma.ι M j) ≫ g) : f = g := by
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  apply (moduleToHomotopy_map_eq_iff A D f g).2
  apply moduleCoproduct_homotopy_of_components A D M f g
  intro j
  apply (moduleToHomotopy_map_eq_iff A D _ _).1
  simpa only [CategoryTheory.Functor.map_comp] using h j

def moduleHomotopyCofan (M : J → ModuleCategory A D) :
    Cofan (fun j => (moduleToHomotopy A D).obj (M j)) :=
  Cofan.mk ((moduleToHomotopy A D).obj (∐ M))
    (fun j => (moduleToHomotopy A D).map (Sigma.ι M j))

def moduleHomotopyCofanDesc (M : J → ModuleCategory A D)
    (s : Cofan (fun j => (moduleToHomotopy A D).obj (M j))) :
    (moduleToHomotopy A D).obj (∐ M) ⟶ s.pt :=
  (moduleToHomotopy A D).map (Sigma.desc (fun j =>
    (moduleToHomotopy A D).preimage (X := M j) (Y := s.pt.as) (s.inj j)))

lemma moduleHomotopyCofanDesc_fac (M : J → ModuleCategory A D)
    (s : Cofan (fun j => (moduleToHomotopy A D).obj (M j))) (j : J) :
    (moduleToHomotopy A D).map (Sigma.ι M j) ≫ moduleHomotopyCofanDesc A D M s = s.inj j := by
  unfold moduleHomotopyCofanDesc
  rw [← CategoryTheory.Functor.map_comp, Sigma.ι_comp_desc]
  exact (moduleToHomotopy A D).map_preimage _

def moduleHomotopyCofanIsColimit (M : J → ModuleCategory A D) :
    IsColimit (moduleHomotopyCofan A D M) :=
  Cofan.IsColimit.mk _ (moduleHomotopyCofanDesc A D M)
    (moduleHomotopyCofanDesc_fac A D M) (by
      intro s m hm
      apply moduleHomotopyCoproduct_hom_ext A D M
      intro j
      exact (hm j).trans (moduleHomotopyCofanDesc_fac A D M s j).symm)

instance moduleHomotopyHasCoproductsOfShape :
    HasColimitsOfShape (Discrete J) (ModuleHomotopyCategory A D) where
  has_colimit F := by
    let M : J → ModuleCategory A D := fun j => (F.obj ⟨j⟩).as
    have : HasColimit (Discrete.functor (fun j => (moduleToHomotopy A D).obj (M j))) :=
      ⟨⟨moduleHomotopyCofan A D M, moduleHomotopyCofanIsColimit A D M⟩⟩
    let e : Discrete.functor (fun j => (moduleToHomotopy A D).obj (M j)) ≅ F :=
      Discrete.natIso (fun j => Iso.refl (F.obj j))
    exact hasColimit_of_iso e.symm


instance moduleToHomotopyPreservesCoproduct (M : J → ModuleCategory A D) :
    PreservesColimit (Discrete.functor M) (moduleToHomotopy A D) := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
  exact (isColimitMapCoconeCofanMkEquiv (moduleToHomotopy A D) M _).symm
    (moduleHomotopyCofanIsColimit A D M)

end SerrePositivity.DifferentialGraded
end

end HomotopyCoproductUniversal

/-! ## HomRight（旧 SerrePositivity/DifferentialGraded/Module/HomRight.lean） -/

/-! # 左dg加群から固定終域への右Hom加群 -/

@[expose] public section HomRight
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 値がHom_A(N(x),T)である右dg加群。NのoppositeとCh(A)の代表加群の合成。 -/
def homRightModule (N : LeftModule A D) (T : Complex A) : RightModule A D :=
  N.op.comp (homContravariantDG A T)

lemma homRightModule_obj (N : LeftModule A D) (T : Complex A) (x : Dᵒᵖ) :
    (homRightModule A D N T).obj x = homComplex A (N.obj x.unop) T := rfl

/-- 任意次数の作用はNの作用による符号付き前合成である。 -/
lemma homRightModule_action (N : LeftModule A D) (T : Complex A) (x y : Dᵒᵖ)
    (p q n : ℤ) (hn : q + p = n) (f : GradedHom A x y p)
    (g : Homogeneous (N.obj x.unop) T q) :
    (((homRightModule A D N T).map x y).f p f).v q n hn g =
    (p * q).negOnePow • (((N.map y.unop x.unop).f p f).comp g (by omega)) := by
  change (((homContravariantDG A T).map (op (N.obj x.unop))
      (op (N.obj y.unop))).f p ((N.map y.unop x.unop).f p f)).v q n hn g = _
  exact homContravariantDG_map_element A T (op (N.obj x.unop)) (op (N.obj y.unop))
    p q n hn ((N.map y.unop x.unop).f p f) g

end SerrePositivity.DifferentialGraded
end

end HomRight

/-! ## HomRightContra（旧 SerrePositivity/DifferentialGraded/Module/HomRightContra.lean） -/

/-! # 右Hom加群の左加群変数に関する反変Hom作用 -/

@[expose] public section HomRightContra
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群を評価し、固定終域への反変Homを取るdg関手。 -/
def homRightContraEvaluation (T : Complex A) (x : D) :
    DGFunctor A (LeftModule A D)ᵒᵖ (Complex A) :=
  (leftModuleEvaluationDG A D x).op.comp (homContravariantDG A T)

/-- 反変Hom作用を各D対象でのchain mapとして保持する。 -/
def homRightContraApp (N N' : LeftModule A D) (T : Complex A) (x : Dᵒᵖ) :
    leftModuleHom A D N N' ⟶ homComplex A
      ((homRightModule A D N' T).obj x) ((homRightModule A D N T).obj x) :=
  (homRightContraEvaluation A D T x.unop).map (op N') (op N)

lemma homRightContraApp_element (N N' : LeftModule A D) (T : Complex A) (x : Dᵒᵖ)
    {k q n : ℤ} (hn : q + k = n) (τ : (leftModuleHom A D N N').X k)
    (g : Homogeneous (N'.obj x.unop) T q) :
    (((homRightContraApp A D N N' T x).f k τ).v q n hn) g =
      (k * q).negOnePow • (((leftModuleHomπ A D N N' x.unop).f k τ).comp g (by omega)) := by
  change (((homContravariantDG A T).map (op (N'.obj x.unop)) (op (N.obj x.unop))).f k
    ((leftModuleHomπ A D N N' x.unop).f k τ)).v q n hn g = _
  exact homContravariantDG_map_element A T (op (N'.obj x.unop)) (op (N.obj x.unop))
    k q n hn ((leftModuleHomπ A D N N' x.unop).f k τ) g

lemma homRightContra_action (N N' : LeftModule A D) (T : Complex A) (x y : Dᵒᵖ)
    (k p r n : ℤ) (hn : r + (k + p) = n) (τ : (leftModuleHom A D N N').X k)
    (f : GradedHom A x y p) (g : Homogeneous (N'.obj x.unop) T r) :
    ((homRightContraApp A D N N' T y).f k τ).v (r + p) n (by omega)
      (moduleAction A (homRightModule A D N' T) f g rfl) =
    (k * p).negOnePow • moduleAction A (homRightModule A D N T) f
      (((homRightContraApp A D N N' T x).f k τ).v r (r + k) rfl g) (by omega) := by
  change ((homRightContraApp A D N N' T y).f k τ).v (r + p) n (by omega)
      ((((homRightModule A D N' T).map x y).f p f).v r (r + p) rfl g) =
    (k * p).negOnePow • (((homRightModule A D N T).map x y).f p f).v (r + k) n (by omega)
      (((homRightContraApp A D N N' T x).f k τ).v r (r + k) rfl g)
  rw [homRightContraApp_element, homRightContraApp_element,
    homRightModule_action, homRightModule_action, Cochain.comp_units_smul,
    Cochain.comp_units_smul]
  rw [← Cochain.comp_assoc _ _ g rfl (by omega : p + r = r + p) (by omega),
    ← Cochain.comp_assoc _ _ g (by omega : p + k = k + p) (by omega) (by omega)]
  rw [leftModuleHomElement_naturality A D k τ y.unop x.unop p f, Cochain.units_smul_comp]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : k * p + (p * (r + k) + (k * r + k * p)) =
      k * (r + p) + p * r + 2 * (k * p) := by ring
  rw [hs, Int.negOnePow_add (k * (r + p) + p * r) (2 * (k * p)),
    Int.negOnePow_two_mul, mul_one]

/-- 左加群Homをパラメータとする、右Hom加群間の全次数自然な族。 -/
def homRightContraParam (N N' : LeftModule A D) (T : Complex A) :
    ModuleParamTrans A D (leftModuleHom A D N N')
      (homRightModule A D N' T) (homRightModule A D N T) where
  app := homRightContraApp A D N N' T
  naturality := moduleParamNaturality_of_apply A
    (M := homRightModule A D N' T) (N := homRightModule A D N T)
    (homRightContraApp A D N N' T) (homRightContra_action A D N N' T)

/-- 左加群変数の反変Hom写像。 -/
def homRightContraHomMap (N N' : LeftModule A D) (T : Complex A) :
    leftModuleHom A D N N' ⟶
      moduleHom A D (homRightModule A D N' T) (homRightModule A D N T) :=
  (moduleHomEquiv A D _ _ _).symm (homRightContraParam A D N N' T)

@[reassoc (attr := simp)]
lemma homRightContraHomMap_π (N N' : LeftModule A D) (T : Complex A) (x : D) :
    homRightContraHomMap A D N N' T ≫
      moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x =
    homRightContraApp A D N N' T (op x) :=
  moduleHomEquiv_symm_π A D _ _ _ (homRightContraParam A D N N' T) x

lemma homRightContraHomMap_element (N N' : LeftModule A D) (T : Complex A) (x : D)
    {p q n : ℤ} (hn : q + p = n) (τ : (leftModuleHom A D N N').X p)
    (g : Homogeneous (N'.obj x) T q) :
    (((moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
      ((homRightContraHomMap A D N N' T).f p τ)).v q n hn) g =
    (p * q).negOnePow • (((leftModuleHomπ A D N N' x).f p τ).comp g (by omega)) := by
  have h := congrArg (fun t => t.f p τ) (homRightContraHomMap_π A D N N' T x)
  exact (congrArg (fun c => c.v q n hn g) h).trans
    (homRightContraApp_element A D N N' T (op x) hn τ g)

lemma homRightContraHomMap_π_apply (N N' : LeftModule A D) (T : Complex A) (x : D)
    (p : ℤ) (τ : (leftModuleHom A D N N').X p) :
    (moduleHomπ A D (homRightModule A D N' T) (homRightModule A D N T) x).f p
      ((homRightContraHomMap A D N N' T).f p τ) =
    ((homRightContraEvaluation A D T x).map (op N') (op N)).f p τ :=
  congrArg (fun t => t.f p τ) (homRightContraHomMap_π A D N N' T x)

lemma homRightContraHomMap_unit (N : LeftModule A D) (T : Complex A) :
    (homRightContraHomMap A D N N T).f 0 (unitElement A N).val =
      (unitElement A (homRightModule A D N T)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [homRightContraHomMap_π_apply]
  exact (DGFunctor.map_unitElement A (homRightContraEvaluation A D T x) (op N)).trans
    (DGFunctor.map_unitElement A (moduleEvaluationDG A D x) (homRightModule A D N T)).symm

lemma homRightContraHomMap_forward (T : Complex A) (N₀ N₁ N₂ : (LeftModule A D)ᵒᵖ)
    {p q n : ℤ} (f : GradedHom A N₀ N₁ p) (g : GradedHom A N₁ N₂ q) (hn : p + q = n) :
    (homRightContraHomMap A D N₂.unop N₀.unop T).f n (forward A f g hn) =
      forward A (D := RightModule A D)
        ((homRightContraHomMap A D N₁.unop N₀.unop T).f p f)
        ((homRightContraHomMap A D N₂.unop N₁.unop T).f q g) hn := by
  apply moduleHomElement_ext A D
  intro x
  rw [homRightContraHomMap_π_apply]
  have he := DGFunctor.map_forward A (moduleEvaluationDG A D x)
    ((homRightContraHomMap A D N₁.unop N₀.unop T).f p f)
    ((homRightContraHomMap A D N₂.unop N₁.unop T).f q g) hn
  change (moduleHomπ A D (homRightModule A D N₀.unop T)
      (homRightModule A D N₂.unop T) x).f n
      (forward A (D := RightModule A D)
        ((homRightContraHomMap A D N₁.unop N₀.unop T).f p f)
        ((homRightContraHomMap A D N₂.unop N₁.unop T).f q g) hn) =
    forward A (D := Complex A)
      ((moduleHomπ A D (homRightModule A D N₀.unop T) (homRightModule A D N₁.unop T) x).f p
        ((homRightContraHomMap A D N₁.unop N₀.unop T).f p f))
      ((moduleHomπ A D (homRightModule A D N₁.unop T) (homRightModule A D N₂.unop T) x).f q
        ((homRightContraHomMap A D N₂.unop N₁.unop T).f q g)) hn at he
  rw [homRightContraHomMap_π_apply, homRightContraHomMap_π_apply] at he
  exact (DGFunctor.map_forward A (homRightContraEvaluation A D T x) f g hn).trans he.symm

/-- 固定終域Tへの右Hom加群は左加群変数に反変な実際のdg関手。 -/
def homRightContraDG (T : Complex A) : DGFunctor A (LeftModule A D)ᵒᵖ (RightModule A D) :=
  DGFunctor.ofHomMaps A (fun N => homRightModule A D N.unop T)
    (fun N N' => homRightContraHomMap A D N'.unop N.unop T)
    (fun N => homRightContraHomMap_unit A D N.unop T)
    (fun N₀ N₁ N₂ _ _ _ hn f g => homRightContraHomMap_forward A D T N₀ N₁ N₂ f g hn)

end SerrePositivity.DifferentialGraded
end

end HomRightContra

/-! ## HomRightContraMaps（旧 SerrePositivity/DifferentialGraded/Module/HomRightContraMaps.lean） -/

/-! # 左加群変数の反変Hom写像と閉零射の比較 -/

@[expose] public section HomRightContraMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftModuleEvaluation_closedMap (x : D) {N N' : LeftModuleCategory A D} (f : N ⟶ N') :
    closedMap A ((leftModuleEvaluation A D x).map f) =
    ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      leftModuleHomπ A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') x :=
  closedMap_mapFromUnit A _ _ _

lemma homRightContraHomMap_closed_component {N N' : LeftModuleCategory A D} (f : N ⟶ N')
    (T : Complex A) (x : D) :
    (ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      homRightContraHomMap A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') T) ≫
      moduleHomπ A D (homRightModule A D (ForgetEnrichment.to (Complex A) N') T)
        (homRightModule A D (ForgetEnrichment.to (Complex A) N) T) x =
      closedMap A (homPrecompose ((leftModuleEvaluation A D x).map f) T) := by
  rw [Category.assoc, homRightContraHomMap_π]
  change (ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫
      leftModuleHomπ A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) N') x) ≫
      (homContravariantDG A T).map
        (op ((ForgetEnrichment.to (Complex A) N').obj x))
        (op ((ForgetEnrichment.to (Complex A) N).obj x)) = _
  have h := congrArg (fun t => t ≫ (homContravariantDG A T).map
      (op ((ForgetEnrichment.to (Complex A) N').obj x))
      (op ((ForgetEnrichment.to (Complex A) N).obj x))) (leftModuleEvaluation_closedMap A D x f)
  exact h.symm.trans (homContravariantDG_closedMap A ((leftModuleEvaluation A D x).map f) T)

/-- 豊穣oppositeと閉零圏のoppositeの既存比較を介した反変右Hom関手。 -/
def homRightContraFunctor (T : Complex A) : (LeftModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D :=
  (forgetEnrichmentOppositeEquivalence (Complex A) (LeftModule A D)).inverse ⋙
    (homRightContraDG A D T).onClosed

@[simp]
lemma homRightContraFunctor_map_eval {N N' : LeftModuleCategory A D} (f : N ⟶ N')
    (T : Complex A) (x : D) :
    (moduleEvaluation A D x).map ((homRightContraFunctor A D T).map f.op) =
      homPrecompose ((leftModuleEvaluation A D x).map f) T := by
  have h := congrArg (mapFromUnit A _ _) (homRightContraHomMap_closed_component A D f T x)
  rw [mapFromUnit_closedMap] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end HomRightContraMaps

/-! ## HomRightFunctor（旧 SerrePositivity/DifferentialGraded/Module/HomRightFunctor.lean） -/

/-! # 右Hom加群の終域変数の関手性 -/

@[expose] public section HomRightFunctor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma homRightModule_postcompose_naturality (N : LeftModule A D)
    {T T' : Complex A} (f : T ⟶ T') (x y : Dᵒᵖ) :
    (homRightModule A D N T).map x y ≫
      homPostcompose (homComplex A (N.obj x.unop) T) (homPostcompose (N.obj y.unop) f) =
    (homRightModule A D N T').map x y ≫
      homPrecompose (homPostcompose (N.obj x.unop) f) (homComplex A (N.obj y.unop) T') := by
  apply closedFamily_of_action A
    (M := homRightModule A D N T) (N := homRightModule A D N T')
    (fun x => homPostcompose (N.obj x.unop) f)
  intro x y p r n hn α g
  change (homPostcompose (N.obj y.unop) f).f n
      ((((homRightModule A D N T).map x y).f p α).v r n hn g) =
    (((homRightModule A D N T').map x y).f p α).v r n hn
      ((homPostcompose (N.obj x.unop) f).f r g)
  rw [homRightModule_action, homRightModule_action]
  simp only [Units.smul_def, map_zsmul, homPostcompose_apply]
  congr 1
  exact Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _

variable [Small.{u} D]

/-- Hom加群の値域での後合成を全dg自然な閉零射へ束ねる。 -/
def homRightModuleMap (N : LeftModule A D) {T T' : Complex A} (f : T ⟶ T') :
    ForgetEnrichment.of (Complex A) (homRightModule A D N T) ⟶
      ForgetEnrichment.of (Complex A) (homRightModule A D N T') :=
  moduleMorphismMk A D (fun x => homPostcompose (N.obj x.unop) f)
    (homRightModule_postcompose_naturality A D N f)

@[simp]
lemma homRightModuleMap_eval (N : LeftModule A D) {T T' : Complex A}
    (f : T ⟶ T') (x : D) :
    (moduleEvaluation A D x).map (homRightModuleMap A D N f) = homPostcompose (N.obj x) f :=
  moduleMorphismMk_eval A D _ _ x

/-- tensor–Hom随伴の右側となる、固定Nからの右Hom加群関手。 -/
def homRightFunctor (N : LeftModule A D) : Complex A ⥤ ModuleCategory A D where
  obj T := ForgetEnrichment.of (Complex A) (homRightModule A D N T)
  map f := homRightModuleMap A D N f
  map_id T := by
    apply moduleMorphism_ext
    intro x
    rw [homRightModuleMap_eval, CategoryTheory.Functor.map_id]
    exact (homFunctor (N.obj x)).map_id T
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, homRightModuleMap_eval,
      homRightModuleMap_eval, homRightModuleMap_eval]
    exact (homFunctor (N.obj x)).map_comp f g

end SerrePositivity.DifferentialGraded
end

end HomRightFunctor

/-! ## HomRightEnriched（旧 SerrePositivity/DifferentialGraded/Module/HomRightEnriched.lean） -/

/-! # 右Hom加群の終域変数のdg関手性 -/

@[expose] public section HomRightEnriched
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma homRightPostcompose_action (N : LeftModule A D) (T T' : Complex A)
    (x y : Dᵒᵖ) (k p r n : ℤ) (hn : r + (k + p) = n)
    (t : Homogeneous T T' k) (f : GradedHom A x y p)
    (v : Homogeneous (N.obj x.unop) T r) :
    (((homCovariantDG A (N.obj y.unop)).map T T').f k t).v (r + p) n (by omega)
      (moduleAction A (homRightModule A D N T) f v rfl) =
    (k * p).negOnePow • moduleAction A (homRightModule A D N T') f
      ((((homCovariantDG A (N.obj x.unop)).map T T').f k t).v r (r + k) rfl v) (by omega) := by
  change (((homCovariantDG A (N.obj y.unop)).map T T').f k t).v (r + p) n (by omega)
      ((((homRightModule A D N T).map x y).f p f).v r (r + p) rfl v) =
    (k * p).negOnePow • (((homRightModule A D N T').map x y).f p f).v (r + k) n (by omega)
      ((((homCovariantDG A (N.obj x.unop)).map T T').f k t).v r (r + k) rfl v)
  rw [homCovariantDG_map_element, homCovariantDG_map_element,
    homRightModule_action, homRightModule_action, Cochain.units_smul_comp]
  rw [Cochain.comp_assoc _ v t (by omega : p + r = r + p) rfl (by omega)]
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : k * p + p * (r + k) = p * r + 2 * (k * p) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 各対象での後合成を、主Hom endの全次数自然性を持つ族として保持する。 -/
def homRightParam (N : LeftModule A D) (T T' : Complex A) :
    ModuleParamTrans A D (homComplex A T T') (homRightModule A D N T)
      (homRightModule A D N T') where
  app x := (homCovariantDG A (N.obj x.unop)).map T T'
  naturality := moduleParamNaturality_of_apply A
    (M := homRightModule A D N T) (N := homRightModule A D N T')
    (fun x => (homCovariantDG A (N.obj x.unop)).map T T')
    (homRightPostcompose_action A D N T T')

variable [Small.{u} D]

/-- 終域の主Hom全体から右Hom加群間の主Hom endへのchain map。 -/
def homRightHomMap (N : LeftModule A D) (T T' : Complex A) :
    homComplex A T T' ⟶ moduleHom A D (homRightModule A D N T) (homRightModule A D N T') :=
  (moduleHomEquiv A D _ _ _).symm (homRightParam A D N T T')

@[reassoc (attr := simp)]
lemma homRightHomMap_π (N : LeftModule A D) (T T' : Complex A) (x : D) :
    homRightHomMap A D N T T' ≫
      moduleHomπ A D (homRightModule A D N T) (homRightModule A D N T') x =
    (homCovariantDG A (N.obj x)).map T T' :=
  moduleHomEquiv_symm_π A D _ _ _ (homRightParam A D N T T') x

lemma homRightHomMap_element (N : LeftModule A D) (T T' : Complex A) (x : D)
    {p q n : ℤ} (hn : q + p = n) (f : Homogeneous T T' p)
    (g : Homogeneous (N.obj x) T q) :
    (((moduleHomπ A D (homRightModule A D N T) (homRightModule A D N T') x).f p
      ((homRightHomMap A D N T T').f p f)).v q n hn) g = g.comp f hn := by
  have h := congrArg (fun t => t.f p f) (homRightHomMap_π A D N T T' x)
  exact (congrArg (fun c => c.v q n hn g) h).trans
    (homCovariantDG_map_element A (N.obj x) T T' p q n hn f g)

lemma homRightHomMap_π_apply (N : LeftModule A D) (T T' : Complex A) (x : D)
    (p : ℤ) (f : Homogeneous T T' p) :
    (moduleHomπ A D (homRightModule A D N T) (homRightModule A D N T') x).f p
      ((homRightHomMap A D N T T').f p f) =
    ((homCovariantDG A (N.obj x)).map T T').f p f :=
  congrArg (fun t => t.f p f) (homRightHomMap_π A D N T T' x)

lemma homRightHomMap_unit (N : LeftModule A D) (T : Complex A) :
    (homRightHomMap A D N T T).f 0 (unitElement A T).val =
      (unitElement A (homRightModule A D N T)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [homRightHomMap_π_apply]
  exact (DGFunctor.map_unitElement A (homCovariantDG A (N.obj x)) T).trans
    (DGFunctor.map_unitElement A (moduleEvaluationDG A D x) (homRightModule A D N T)).symm

lemma homRightHomMap_forward (N : LeftModule A D) {T T' T'' : Complex A}
    {p q n : ℤ} (f : Homogeneous T T' p) (g : Homogeneous T' T'' q) (hn : p + q = n) :
    (homRightHomMap A D N T T'').f n (forward A (D := Complex A) f g hn) =
      forward A (D := RightModule A D)
        ((homRightHomMap A D N T T').f p f) ((homRightHomMap A D N T' T'').f q g) hn := by
  apply moduleHomElement_ext A D
  intro x
  rw [homRightHomMap_π_apply]
  have he := DGFunctor.map_forward A (moduleEvaluationDG A D x)
    ((homRightHomMap A D N T T').f p f) ((homRightHomMap A D N T' T'').f q g) hn
  change (moduleHomπ A D (homRightModule A D N T) (homRightModule A D N T'') x).f n
      (forward A (D := RightModule A D)
        ((homRightHomMap A D N T T').f p f) ((homRightHomMap A D N T' T'').f q g) hn) =
    forward A (D := Complex A)
      ((moduleHomπ A D (homRightModule A D N T) (homRightModule A D N T') x).f p
        ((homRightHomMap A D N T T').f p f))
      ((moduleHomπ A D (homRightModule A D N T') (homRightModule A D N T'') x).f q
        ((homRightHomMap A D N T' T'').f q g)) hn at he
  rw [homRightHomMap_π_apply, homRightHomMap_π_apply] at he
  exact (DGFunctor.map_forward A (homCovariantDG A (N.obj x)) f g hn).trans he.symm

/-- 固定左加群Nに対する右Hom加群の実際のCh(A)豊穣関手。 -/
def homRightDG (N : LeftModule A D) : DGFunctor A (Complex A) (RightModule A D) :=
  DGFunctor.ofHomMaps A (homRightModule A D N) (homRightHomMap A D N)
    (homRightHomMap_unit A D N)
    (fun _ _ _ _ _ _ hn f g => homRightHomMap_forward A D N f g hn)

/-- 全Hom写像の閉零射への制限は先行するhomRightModuleMapと一致する。 -/
lemma homRightHomMap_closedMap (N : LeftModule A D) {T T' : Complex A} (f : T ⟶ T') :
    closedMap A f ≫ homRightHomMap A D N T T' =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D)
        (X := homRightModule A D N T) (Y := homRightModule A D N T')
        (homRightModuleMap A D N f) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, homRightHomMap_π]
  have h := moduleEvaluation_closedMap A D x (homRightModuleMap A D N f)
  rw [homRightModuleMap_eval] at h
  exact (homCovariantDG_closedMap A (N.obj x) f).trans h

end SerrePositivity.DifferentialGraded
end

end HomRightEnriched

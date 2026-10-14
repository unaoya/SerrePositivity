module
public import SerrePositivity.DifferentialGraded.Complexes.Biproduct
public import SerrePositivity.DifferentialGraded.Module.Zero
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # objectwise 二項直和の全次数作用と普遍性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 対象での直和に対角の全次数作用を与えた右 dg 加群。 -/
abbrev biprodModule (M N : RightModule A D) : RightModule A D where
  obj x := M.obj x ⊞ N.obj x
  map x y := biprodHomMap (M.map x y) (N.map x y)
  map_id x := by
    change eId (Complex A) x ≫ biprodHomMap (M.map x x) (N.map x x) =
      identity (M.obj x ⊞ N.obj x)
    rw [biprodHomMap_precomp, M.toFunctor.map_id, N.toFunctor.map_id]
    exact biprodHomMap_identity _ _
  map_comp x y z := by
    change eComp (Complex A) x y z ≫ biprodHomMap (M.map x z) (N.map x z) =
      (biprodHomMap (M.map x y) (N.map x y) ⊗ₘ
        biprodHomMap (M.map y z) (N.map y z)) ≫ enrichedComposition _ _ _
    rw [biprodHomMap_precomp, M.toFunctor.map_comp, N.toFunctor.map_comp,
      biprodHomMap_comp]
    rfl

/-- 全次数作用の行列は対角である。 -/
lemma biprodModule_map_v (M N : RightModule A D) (x y : Dᵒᵖ)
    (p i j : ℤ) (hij : i + p = j) (f : GradedHom A x y p) :
    (((biprodModule M N).map x y).f p f).v i j hij =
      (biprod.fst : M.obj x ⊞ N.obj x ⟶ M.obj x).f i ≫
        ((M.map x y).f p f).v i j hij ≫
          (biprod.inl : M.obj y ⟶ M.obj y ⊞ N.obj y).f j +
      (biprod.snd : M.obj x ⊞ N.obj x ⟶ N.obj x).f i ≫
        ((N.map x y).f p f).v i j hij ≫
          (biprod.inr : N.obj y ⟶ M.obj y ⊞ N.obj y).f j :=
  biprodHomMap_v _ _ p i j hij f

variable (A D) [Small.{u} D]

/-- 閉零加群圏の具体的 objectwise 二項直和。 -/
abbrev moduleBiprod (M N : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (biprodModule
    (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))

/-- 第一射影は全次数自然な加群射。 -/
def moduleBiprodFst (M N : ModuleCategory A D) : moduleBiprod A D M N ⟶ M :=
  moduleMorphismMk A D
    (M := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => biprod.fst)
    (fun _ _ => biprodHomMap_fst _ _)

/-- 第二射影は全次数自然な加群射。 -/
def moduleBiprodSnd (M N : ModuleCategory A D) : moduleBiprod A D M N ⟶ N :=
  moduleMorphismMk A D
    (M := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (N := ForgetEnrichment.to (Complex A) N) (fun _ => biprod.snd)
    (fun _ _ => biprodHomMap_snd _ _)

/-- 第一包含は全次数自然な加群射。 -/
def moduleBiprodInl (M N : ModuleCategory A D) : M ⟶ moduleBiprod A D M N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (fun _ => biprod.inl)
    (fun _ _ => (biprodHomMap_inl _ _).symm)

/-- 第二包含は全次数自然な加群射。 -/
def moduleBiprodInr (M N : ModuleCategory A D) : N ⟶ moduleBiprod A D M N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) N)
    (N := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (fun _ => biprod.inr)
    (fun _ _ => (biprodHomMap_inr _ _).symm)

@[simp] lemma moduleBiprodFst_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodFst A D M N) = biprod.fst :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodSnd_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodSnd A D M N) = biprod.snd :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodInl_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodInl A D M N) = biprod.inl :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodInr_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodInr A D M N) = biprod.inr :=
  moduleMorphismMk_eval A D _ _ x

/-- objectwise 直和の射影と包含をまとめた Mathlib の bicone。 -/
def moduleBinaryBicone (M N : ModuleCategory A D) : BinaryBicone M N where
  pt := moduleBiprod A D M N
  fst := moduleBiprodFst A D M N
  snd := moduleBiprodSnd A D M N
  inl := moduleBiprodInl A D M N
  inr := moduleBiprodInr A D M N
  inl_fst := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleBiprodFst_eval, moduleBiprodInl_eval]
    exact biprod.inl_fst (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inl_snd := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, Functor.map_zero,
      moduleBiprodSnd_eval, moduleBiprodInl_eval]
    exact biprod.inl_snd (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inr_fst := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, Functor.map_zero,
      moduleBiprodFst_eval, moduleBiprodInr_eval]
    exact biprod.inr_fst (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inr_snd := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleBiprodSnd_eval, moduleBiprodInr_eval]
    exact biprod.inr_snd (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)

/-- bicone の恒等分解は objectwise 直和の恒等分解。 -/
lemma moduleBinaryBicone_total (M N : ModuleCategory A D) :
    (moduleBinaryBicone A D M N).fst ≫ (moduleBinaryBicone A D M N).inl +
      (moduleBinaryBicone A D M N).snd ≫ (moduleBinaryBicone A D M N).inr =
        𝟙 (moduleBinaryBicone A D M N).pt := by
  apply moduleMorphism_ext
  intro x
  change (moduleEvaluation A D x).map
    (moduleBiprodFst A D M N ≫ moduleBiprodInl A D M N +
      moduleBiprodSnd A D M N ≫ moduleBiprodInr A D M N) =
        (moduleEvaluation A D x).map (𝟙 (moduleBiprod A D M N))
  simp only [Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, moduleBiprodFst_eval, moduleBiprodSnd_eval,
    moduleBiprodInl_eval, moduleBiprodInr_eval]
  exact biprod.total (X := (moduleEvaluation A D x).obj M)
    (Y := (moduleEvaluation A D x).obj N)

/-- objectwise 直和は積・余積の両方の普遍性を満たす。 -/
def moduleBinaryBiconeIsBilimit (M N : ModuleCategory A D) :
    (moduleBinaryBicone A D M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (moduleBinaryBicone_total A D M N)

instance moduleHasBinaryBiproducts : HasBinaryBiproducts (ModuleCategory A D) where
  has_binary_biproduct M N :=
    hasBinaryBiproduct_of_total _ (moduleBinaryBicone_total A D M N)

/-- 零対象と二項直和から有限直和を供給する。一般の構成は Mathlib を再利用。 -/
instance moduleHasFiniteBiproducts : HasFiniteBiproducts (ModuleCategory A D) := by
  let : HasFiniteProducts (ModuleCategory A D) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- 具体的 objectwise 直和と選ばれた圏の直和の標準同型。 -/
def moduleBiprodIso (M N : ModuleCategory A D) : moduleBiprod A D M N ≅ M ⊞ N :=
  biprod.uniqueUpToIso M N (moduleBinaryBiconeIsBilimit A D M N)

/-- 評価の加法性から Mathlib の二項直和保存を導く。 -/
instance moduleEvaluationPreservesBinaryBiproducts (x : D) :
    PreservesBinaryBiproducts (moduleEvaluation A D x) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- 評価は選ばれた圏の直和を既存複体の直和へ移す。 -/
def moduleEvaluationBiprodIso (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (M ⊞ N) ≅
      (moduleEvaluation A D x).obj M ⊞ (moduleEvaluation A D x).obj N :=
  (moduleEvaluation A D x).mapBiprod M N

/-- 評価による比較同型は第一射影と可換。 -/
@[reassoc]
lemma moduleEvaluationBiprodIso_fst (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluationBiprodIso A D M N x).hom ≫ biprod.fst =
      (moduleEvaluation A D x).map (biprod.fst : M ⊞ N ⟶ M) := by
  rw [moduleEvaluationBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

/-- 評価による比較同型は第二射影と可換。 -/
@[reassoc]
lemma moduleEvaluationBiprodIso_snd (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluationBiprodIso A D M N x).hom ≫ biprod.snd =
      (moduleEvaluation A D x).map (biprod.snd : M ⊞ N ⟶ N) := by
  rw [moduleEvaluationBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _
end SerrePositivity.DifferentialGraded

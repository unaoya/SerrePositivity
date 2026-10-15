module
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements
public import SerrePositivity.DifferentialGraded.Module.HomRight
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 右Hom加群の左加群変数に関する反変Hom作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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

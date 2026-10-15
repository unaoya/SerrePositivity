module
public import SerrePositivity.DifferentialGraded.Complexes.HomCovariant
public import SerrePositivity.DifferentialGraded.Module.HomRightFunctor
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 右Hom加群の終域変数のdg関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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

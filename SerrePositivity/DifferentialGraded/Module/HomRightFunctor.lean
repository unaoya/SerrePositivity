module
public import SerrePositivity.DifferentialGraded.Module.HomRight
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 右Hom加群の終域変数の関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
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

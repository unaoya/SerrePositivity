module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # bimoduleの右作用を左加群の主Hom endへ転置する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 交換則を左C作用の後に右B作用を行う向きへ書き直す。 -/
lemma transposeInterchange (M : Bimodule A B C) {b b' : Bᵒᵖ} {c c' : C} {p q : ℤ}
    (f : GradedHom A b b' p) (g : GradedHom A c c' q) :
    (M.leftCochain g b.unop).comp (((M.rightAt c').map b b').f p f)
      rfl =
    (p * q).negOnePow • ((((M.rightAt c).map b b').f p f).comp
      (M.leftCochain g b'.unop) (by omega)) := by
  have h := congrArg (fun t => (p * q).negOnePow • t) (M.interchange f g)
  rw [mul_comm q p, smul_smul, Int.units_mul_self, one_smul] at h
  simpa only [Opposite.op_unop] using h.symm

variable [Small.{u} C]

/-- 右BのHomをパラメータにした全次数自然な左C加群間の変換。 -/
def transposeParam (M : Bimodule A B C) (b b' : Bᵒᵖ) :
    ModuleParamTrans A Cᵒᵖ (b ⟶[Complex A] b')
      (M.leftAt b.unop).toRightOpposite (M.leftAt b'.unop).toRightOpposite where
  app c := (M.rightAt c.unop.unop).map b b'
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y p q r n hn f g m
    have h := Cochain.congr_v
      (M.transposeInterchange f (c := x.unop.unop) (c' := y.unop.unop) g) r n (by omega)
    rw [Cochain.comp_v _ _ _ r (r + q) n rfl (by omega), Cochain.units_smul_v,
      Cochain.comp_v _ _ _ r (r + p) n rfl (by omega)] at h
    change (((M.rightAt y.unop.unop).map b b').f p f).v (r + q) n (by omega)
        (((𝟙 _ ≫ (M.leftAt b.unop).map x.unop.unop y.unop.unop).f q g).v r (r + q) rfl m) =
      (p * q).negOnePow •
        (((𝟙 _ ≫ (M.leftAt b'.unop).map x.unop.unop y.unop.unop).f q g).v
          (r + p) n (by omega)
          ((((M.rightAt x.unop.unop).map b b').f p f).v r (r + p) rfl m))
    simp only [Category.id_comp]
    exact congrArg (fun t => t m) h

/-- 右B作用の実際の左加群Hom複体への持ち上げ。 -/
def transposeHom (M : Bimodule A B C) (b b' : Bᵒᵖ) :
    (b ⟶[Complex A] b') ⟶ leftModuleHom A C (M.leftAt b.unop) (M.leftAt b'.unop) :=
  (moduleHomEquiv A Cᵒᵖ _ _ _).symm (M.transposeParam b b')

@[reassoc]
lemma transposeHom_π (M : Bimodule A B C) (b b' : Bᵒᵖ) (c : C) :
    M.transposeHom b b' ≫ moduleHomπ A Cᵒᵖ
      (M.leftAt b.unop).toRightOpposite (M.leftAt b'.unop).toRightOpposite (op c) =
    (M.rightAt c).map b b' :=
  moduleHomEquiv_symm_π A Cᵒᵖ _ _ _ (M.transposeParam b b') (op c)

/-- Bᵒᵖから全Hom endを持つ左C加群圏への実際のdg関手。 -/
def transposeDG (M : Bimodule A B C) : DGFunctor A Bᵒᵖ (LeftModule A C) where
  obj b := M.leftAt b.unop
  map := M.transposeHom
  map_id b := by
    apply moduleHom_ext
    intro c
    change eId (Complex A) b ≫ M.transposeHom b b ≫
      moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
        (M.leftAt b.unop).toRightOpposite (op c.unop) =
      moduleIdentity A Cᵒᵖ (M.leftAt b.unop).toRightOpposite ≫
        moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
          (M.leftAt b.unop).toRightOpposite (op c.unop)
    rw [transposeHom_π, moduleIdentity_π]
    change eId (Complex A) b ≫ (M.rightAt c.unop).map b b =
      identity ((M.rightAt c.unop).obj b)
    exact (M.rightAt c.unop).toFunctor.map_id b
  map_comp b b' b'' := by
    apply moduleHom_ext
    intro c
    change eComp (Complex A) b b' b'' ≫ M.transposeHom b b'' ≫
      moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
        (M.leftAt b''.unop).toRightOpposite (op c.unop) =
      (M.transposeHom b b' ⊗ₘ M.transposeHom b' b'') ≫
        moduleComposition A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
          (M.leftAt b'.unop).toRightOpposite (M.leftAt b''.unop).toRightOpposite ≫
            moduleHomπ A Cᵒᵖ (M.leftAt b.unop).toRightOpposite
              (M.leftAt b''.unop).toRightOpposite (op c.unop)
    rw [transposeHom_π, moduleComposition_π, tensorHom_comp_tensorHom_assoc,
      transposeHom_π, transposeHom_π]
    exact (M.rightAt c.unop).toFunctor.map_comp b b' b''

end SerrePositivity.DifferentialGraded.Bimodule

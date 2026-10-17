module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomotopy
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleDGFunctor
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaHom
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 実際の加群係数拡大による全次数Hom要素の合成保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarBaseChange_forward {D : Type v} [DGCategory A D]
    {x y z : D} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) :
    let := φ.toAlgebra
    forward A' (D := ScalarExtension.DGBaseChange φ D)
      (x := x) (y := y) (z := z) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] g) h =
      (1 : A') ⊗ₜ[A] forward A f g h := by
  let := φ.toAlgebra
  change ((ScalarExtension.extension φ).map (eComp (Complex A) x y z)).f n
    ((ScalarExtension.tensorIso φ (x ⟶[Complex A] y) (y ⟶[Complex A] z)).inv.f n
      (ιTensorObj ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))
        ((ScalarExtension.extension φ).obj (y ⟶[Complex A] z)) p q n h
        (((1 : A') ⊗ₜ[A] f) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] g)))) = _
  erw [ScalarExtension.tensorIso_inv_apply φ (x ⟶[Complex A] y) (y ⟶[Complex A] z)
    p q n h f g, ModuleCat.ExtendScalars.map_tmul φ]
  rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 環を変えるHom要素写像。任意次数に定義し、閉性は要求しない。 -/
def scalarModuleHomElement {M N : RightModule A D} {p : ℤ}
    (f : GradedHom A M N p) :
    GradedHom A' (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) p :=
  let := φ.toAlgebra
  (scalarModuleHom φ D M N).f p ((1 : A') ⊗ₜ[A] f)

lemma scalarModuleHomElement_forward {M N P : RightModule A D} {p q n : ℤ}
    (f : GradedHom A M N p) (g : GradedHom A N P q) (h : p + q = n) :
    scalarModuleHomElement φ D (forward A f g h) =
      forward A' (scalarModuleHomElement φ D f) (scalarModuleHomElement φ D g) h := by
  let := φ.toAlgebra
  have hm := (scalarModuleDGFunctor φ D).map_forward A'
    (x := (show ScalarExtension.DGBaseChange φ (RightModule A D) from M))
    (y := N) (z := P) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] g) h
  rw [scalarBaseChange_forward φ f g h] at hm
  exact hm

lemma scalarModuleHomElement_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleHomElement φ D (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A')
        ((ScalarExtension.moduleExtension φ D).map f))).val :=
  scalarModuleHom_cycle φ D f

@[simp] lemma scalarModuleHomElement_zero (M N : RightModule A D) (p : ℤ) :
    scalarModuleHomElement φ D (0 : GradedHom A M N p) = 0 := by
  let := φ.toAlgebra
  simp only [scalarModuleHomElement, TensorProduct.tmul_zero, map_zero]

lemma scalarModuleHomElement_add {M N : RightModule A D} {p : ℤ}
    (f g : GradedHom A M N p) :
    scalarModuleHomElement φ D (f + g) =
      scalarModuleHomElement φ D f + scalarModuleHomElement φ D g := by
  let := φ.toAlgebra
  simp only [scalarModuleHomElement, TensorProduct.tmul_add, map_add]

lemma scalarModuleHomElement_unit (M : RightModule A D) :
    scalarModuleHomElement φ D (unitElement A M).val =
      (unitElement A' (ScalarExtension.rightModule φ D M)).val := by
  have hm := (scalarModuleDGFunctor φ D).map_unitElement A'
    (show ScalarExtension.DGBaseChange φ (RightModule A D) from M)
  rw [scalarUnitElement_one φ (RightModule A D) M] at hm
  exact hm

lemma scalarModuleHomElement_d {M N : RightModule A D} {p q : ℤ}
    (f : GradedHom A M N p) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N)).d p q
        (scalarModuleHomElement φ D f) =
      scalarModuleHomElement φ D ((moduleHom A D M N).d p q f) := by
  let := φ.toAlgebra
  have hc := congrArg (fun k => k ((1 : A') ⊗ₜ[A] f)) ((scalarModuleHom φ D M N).comm p q)
  change _ = (scalarModuleHom φ D M N).f q
    ((ModuleCat.extendScalars φ).map ((moduleHom A D M N).d p q)
      ((1 : A') ⊗ₜ[A] f)) at hc
  erw [ModuleCat.ExtendScalars.map_tmul φ] at hc
  exact hc

end SerrePositivity.DifferentialGraded

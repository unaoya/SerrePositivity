module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNegativeShiftHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberObject
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # shifted cone を標的とする全 Hom の二成分座標

概要：fiber 候補への次数 n+1 の Hom を M への次数 n+1 と N への次数 n に同定する。
方針：shift の斉次単位、全 Hom cone 同型、複体の cone の二成分を順に使う。
規約：全て全 Hom end の線形同値。使われ方：β3 の fiber 境界の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 複体の cone の一つの次数の線形座標。 -/
def dgComplexConeCoordinates {M N : Complex A} (f : M ⟶ N) (n : ℤ) :
    (mappingCone f).X n ≃ₗ[A] (M.X (n + 1) × N.X n) where
  toFun z := ((mappingCone.fst f).val.v n (n + 1) rfl z,
    (mappingCone.snd f).v n n (add_zero n) z)
  invFun z := complexConeElementMk A f n z.1 z.2
  left_inv z := complexConeElementMk_eta A f n z
  right_inv z := Prod.ext (complexConeElementMk_fst A f n z.1 z.2)
    (complexConeElementMk_snd A f n z.1 z.2)
  map_add' z w := by ext <;> exact map_add _ _ _
  map_smul' c z := by ext <;> exact map_smul _ _ _

variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- fiber 候補を標的とする全 Hom end の二成分線形同値。 -/
def dgModuleFiberHomCoordinates (T : ModuleCategory A D) (f : M ⟶ N) (n : ℤ) :
    GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1) ≃ₗ[A]
      (GradedHom A (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) (n + 1) ×
       GradedHom A (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N) n) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) n).trans
      ((((HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).mapIso
        (moduleHomConeIso A D T f).symm).toLinearEquiv).trans
          (dgComplexConeCoordinates A (eHomWhiskerLeft (Complex A) T f) n))).trans
            ((LinearEquiv.refl A _).prodCongr (LinearEquiv.neg A))

end SerrePositivity.InfinityCategories.Project.DerivedCategories

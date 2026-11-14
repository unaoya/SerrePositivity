module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeHomCoordinates

/-! # dg 加群の cone からの Hom の行列微分

概要：全次数の二成分の微分と cone の接続項を明示する。
方針：各対象で descCochain の微分公式を使い、全 Hom end の外延性で戻す。
規約：接続項の符号は (n+2).negOnePow。使われ方：β3 の cofiber 境界の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N X : ModuleCategory A D}

/-- 全 Hom end 内での二成分の復元の微分公式。 -/
lemma dgModuleConeDescElement_differential (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) X) n)
    (b : GradedHom A (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) (n + 1)) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement A D f n a b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement A D f (n + 1)
        (differential A a + (n + 1 + 1).negOnePow • compose A b
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add (n + 1)))
        (differential A b) := by
  apply moduleHomElement_ext A D
  intro x
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) X) x).f (n + 1 + 1)
    ((moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X)).d (n + 1) (n + 1 + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement A D f n a b)) = _
  rw [moduleHomElement_d_π A D (n + 1) (n + 1 + 1) _ x,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_π A D f n a b x,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_π A D f (n + 1) _ _ x, map_add]
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomCompose_π, ← moduleEvaluation_cochain A D x f]
  change _ = mappingCone.descCochain ((moduleEvaluation A D x).map f)
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) X) x).f (n + 1)
      ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) X)).d n (n + 1) a) + _)
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) x).f (n + 1 + 1)
      ((moduleHom A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) X)).d (n + 1) (n + 1 + 1) b)) rfl
  rw [moduleHomElement_d_π A D n (n + 1) a x,
    moduleHomElement_d_π A D (n + 1) (n + 1 + 1) b x]
  exact mappingCone.δ_descCochain _ _ _ rfl _ rfl

/-- 線形同値の逆座標の微分は行列微分に対応する。 -/
lemma dgModuleConeHomCoordinates_symm_differential (f : M ⟶ N) (n : ℤ) (a) (b) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D (X := X) f n).symm (a, b)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHomCoordinates A D f (n + 1)).symm
        (differential A a + (n + 1 + 1).negOnePow • compose A b
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add (n + 1)),
          differential A b) :=
  dgModuleConeDescElement_differential A D f n a b

end SerrePositivity.InfinityCategories.Project.DerivedCategories

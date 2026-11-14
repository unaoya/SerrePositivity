module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # dg 加群の cone への Hom の行列微分

概要：二つの全 Hom end 成分から cone へ復元した元の微分を計算する。
方針：各評価で liftCochain の微分を使い、全 Hom end の外延性で戻す。
規約：第一成分の微分には負号がある。使われ方：β3 の fiber Hom の行列微分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- 全 Hom end の cone への二成分の復元の微分公式。 -/
lemma dgModuleConeLiftElement_differential (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1))
    (b : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) n) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d n (n + 1)
        (moduleConeLiftElement A D f n a b) =
      moduleConeLiftElement A D f (n + 1) (-differential A a)
        (differential A b + compose A
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val a (add_zero (n + 1))) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π A D n (n + 1) _ x,
    moduleConeLiftElement_π A D f n a b x,
    moduleConeLiftElement_π A D f (n + 1) _ _ x, map_neg, map_add,
    moduleHomCompose_π, ← moduleEvaluation_cochain A D x f]
  change _ = mappingCone.liftCochain ((moduleEvaluation A D x).map f)
    (-((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f (n + 1 + 1)
      ((moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M)).d (n + 1) (n + 1 + 1) a)))
    (((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f (n + 1)
      ((moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N)).d n (n + 1) b)) + _) rfl
  rw [moduleHomElement_d_π A D (n + 1) (n + 1 + 1) a x,
    moduleHomElement_d_π A D n (n + 1) b x]
  rw [mappingCone.δ_liftCochain _ _ _ rfl (n + 1 + 1) rfl]
  change _ = (-δ (n + 1) (n + 1 + 1)
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f (n + 1) a)).comp
      (mappingCone.inl ((moduleEvaluation A D x).map f)) (by omega) + _
  exact congrArg (fun z => z + _) (Cochain.neg_comp _ _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # cone への全 Hom の復元と射影

概要：cone への二成分の復元を第一・第二射影で回収する。
方針：全 Hom end の各評価で mapping cone の lift の射影公式を使う。
規約：通常順の斉次合成。使われ方：β3 の fiber 座標と実射影の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- cone lift の第一射影は指定した第一成分。 -/
lemma dgModuleConeLiftElement_fst (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) M) (p := n) (q := 1) (moduleConeFstElement A D f)
      (moduleConeLiftElement A D (T := T) f n a b) rfl = a := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeLiftElement_π, moduleConeFstElement_π]
  exact mappingCone.liftCochain_fst _ _ _ _

/-- cone lift の第二射影は指定した第二成分。 -/
lemma dgModuleConeLiftElement_snd (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) N) (p := n) (q := 0) (moduleConeSndElement A D f)
      (moduleConeLiftElement A D (T := T) f n a b) (add_zero n) = b := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeLiftElement_π, moduleConeSndElement_π]
  exact mappingCone.liftCochain_snd _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

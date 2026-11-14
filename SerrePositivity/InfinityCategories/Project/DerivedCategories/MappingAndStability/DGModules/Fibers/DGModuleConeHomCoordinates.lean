module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeDesc

/-! # dg 加群の cone からの Hom の全次数の線形同値

概要：全 Hom end の cone からの射を包含の二成分と線形に同定する。
方針：成分の復元と一意性を使い、加法・スカラー倍を各評価で確認する。
規約：第一成分は一段低い次数。使われ方：β3 の cofiber 境界の明示解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N X : ModuleCategory A D}

/-- dg 加群の cone から出る射と二つの包含の成分の線形同値。 -/
def dgModuleConeHomCoordinates (f : M ⟶ N) (n : ℤ) :
    GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1) ≃ₗ[A]
    (GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) X) n ×
      GradedHom A (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) X) (n + 1)) where
  toFun z := (compose A z (moduleConeInlElement A D f) (by omega),
    compose A z (moduleConeInrElement A D f) (zero_add (n + 1)))
  invFun z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement A D f n z.1 z.2
  left_inv z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeHom_ext A D f n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_inl A D f n _ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_inr A D f n _ _)
  right_inv z := Prod.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_inl A D f n z.1 z.2)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement_inr A D f n z.1 z.2)
  map_add' z w := by
    apply Prod.ext <;> apply moduleHomElement_ext A D <;> intro x <;>
      simp only [Prod.fst_add, Prod.snd_add, moduleHomCompose_π, map_add] <;>
      exact Cochain.comp_add _ _ _ _
  map_smul' c z := by
    apply Prod.ext <;> apply moduleHomElement_ext A D <;> intro x <;>
      simp only [Prod.smul_fst, Prod.smul_snd, moduleHomCompose_π, map_smul,
        RingHom.id_apply] <;> exact Cochain.comp_smul _ _ _ _

/-- 線形同値の第一座標は左包含との合成。 -/
lemma dgModuleConeHomCoordinates_fst (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1)) :
    (dgModuleConeHomCoordinates A D f n z).1 =
      compose A z (moduleConeInlElement A D f) (by omega) := rfl

/-- 線形同値の第二座標は右包含との合成。 -/
lemma dgModuleConeHomCoordinates_snd (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1)) :
    (dgModuleConeHomCoordinates A D f n z).2 =
      compose A z (moduleConeInrElement A D f) (zero_add (n + 1)) := rfl

/-- 二成分からの逆座標は全 Hom end 内の標準の復元。 -/
lemma dgModuleConeHomCoordinates_symm (f : M ⟶ N) (n : ℤ) (a) (b) :
    (dgModuleConeHomCoordinates A D (X := X) f n).symm (a, b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement A D f n a b := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories

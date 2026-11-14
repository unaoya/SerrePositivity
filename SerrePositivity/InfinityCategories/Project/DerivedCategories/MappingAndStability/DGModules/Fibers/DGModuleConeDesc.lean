module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberHomCoordinates

/-! # dg 加群の cone から出る全次数の成分の復元

概要：二つの Hom 成分から全次数自然な cone からの射を作る。
方針：標準の第一・第二射影と合成し、各評価で descCochain と照合する。
規約：閉元であることはまだ要求しない。使われ方：β3 の cofiber の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N X : ModuleCategory A D}

/-- 全 dg 自然性を保った二成分からの cone 射の復元。 -/
def dgModuleConeDescElement (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) X) n)
    (b : GradedHom A (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) (n + 1)) :
    GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1) :=
  compose A a (moduleConeFstElement A D f) (by omega) +
    compose A b (moduleConeSndElement A D f) (zero_add (n + 1))

/-- 復元した全 Hom 成分を評価すると実際の descCochain になる。 -/
lemma dgModuleConeDescElement_π (f : M ⟶ N) (n : ℤ) (a) (b) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) x).f (n + 1) (dgModuleConeDescElement A D f n a b) =
    mappingCone.descCochain ((moduleEvaluation A D x).map f)
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) X) x).f n a)
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) X) x).f (n + 1) b) rfl := by
  rw [dgModuleConeDescElement, map_add, moduleHomCompose_π, moduleHomCompose_π,
    moduleConeFstElement_π, moduleConeSndElement_π]
  rfl

/-- 復元した射を次数 −1 の左包含で制限すると第一成分になる。 -/
lemma dgModuleConeDescElement_inl (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (dgModuleConeDescElement A D (X := X) f n a b)
      (moduleConeInlElement A D f) (by omega) = a := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, dgModuleConeDescElement_π, moduleConeInlElement_π]
  exact mappingCone.inl_descCochain _ _ _ _

/-- 復元した射を標準の右包含で制限すると第二成分になる。 -/
lemma dgModuleConeDescElement_inr (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (dgModuleConeDescElement A D (X := X) f n a b)
      (moduleConeInrElement A D f) (zero_add (n + 1)) = b := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, dgModuleConeDescElement_π, moduleConeInrElement_π]
  exact mappingCone.inr_descCochain _ _ _ _

/-- 左包含と右包含の成分は全次数の cone 射を一意に決める。 -/
lemma dgModuleConeHom_ext (f : M ⟶ N) (n : ℤ)
    {z w : GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) X) (n + 1)}
    (ha : compose A z (moduleConeInlElement A D f) (show (-1) + (n + 1) = n by omega) =
      compose A w (moduleConeInlElement A D f) (show (-1) + (n + 1) = n by omega))
    (hb : compose A z (moduleConeInrElement A D f) (zero_add (n + 1)) =
      compose A w (moduleConeInrElement A D f) (zero_add (n + 1))) : z = w := by
  apply moduleHomElement_ext A D
  intro x
  apply (mappingCone.ext_cochain_from_iff ((moduleEvaluation A D x).map f) n (n + 1) rfl).2
  constructor
  · have h := congrArg (fun t => (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) X) x).f n t) ha
    simpa only [moduleHomCompose_π, moduleConeInlElement_π] using h
  · have h := congrArg (fun t => (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) X) x).f (n + 1) t) hb
    simpa only [moduleHomCompose_π, moduleConeInrElement_π] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories

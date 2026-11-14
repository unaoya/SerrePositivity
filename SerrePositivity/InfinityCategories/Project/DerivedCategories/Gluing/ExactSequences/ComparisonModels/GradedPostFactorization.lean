module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.GradedPostcompositionClosed

/-! 指定境界元の作用を、全 Hom 円錐比較・閉代表射・Hom 同型の逆へ因子分解する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E) (x y z : C) (l : E)
  (a : ForgetEnrichment.of (Complex R) l ⟶ ForgetEnrichment.of (Complex R) (F.obj z))
  (e : homObject R C x z ≅ homObject R E (F.obj x) (F.obj z))
  (he : F.map x z = e.hom) {P : Complex R}
  (i : Cochain (homObject R C x y) P (-1)) (m : P ⟶ homObject R E (F.obj x) l)
  (h : GradedHom R (F.obj y) l (-1)) (g : GradedHom R y z (-1))

/-- 指定元の関手像が、同じ閉代表射による後合成の像であるという条件。 -/
def dgGluingGradedPostImageCondition : Prop :=
  (F.map y z).f (-1) g =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj y)) a).f (-1) h

variable
  (hi : i.comp (Cochain.ofHom m) (add_zero (-1)) =
    (Cochain.ofHom (F.map x y)).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E (F.obj x) (F.obj y) l).f (-1) h)
      (zero_add (-1)))
  (hg : dgGluingGradedPostImageCondition R C E F y z l a h g)

include he hi hg in
/-- 境界元の像と左包含の作用が一致すれば、native 作用を同じ代表射で回収できる。 -/
lemma dgGluingGradedPost_factorization :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R C x y z).f (-1) g =
    i.comp (Cochain.ofHom (m ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) a ≫ e.inv))
      (add_zero (-1)) := by
  change (F.map y z).f (-1) g =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj y)) a).f (-1) h at hg
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition_naturality R C E F x y z g
  rw [he, hg, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition_postcompose R E
    (F.obj x) (F.obj y) l (F.obj z) a h] at hn
  calc
    _ = (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R C x y z).f (-1) g).comp
        (Cochain.ofHom e.hom) (add_zero (-1))).comp
        (Cochain.ofHom e.inv) (add_zero (-1)) := by
      simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
        Iso.hom_inv_id, Cochain.comp_id]
    _ = ((i.comp (Cochain.ofHom m) (add_zero (-1))).comp
        (Cochain.ofHom (eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) (F.obj x)) a)) (add_zero (-1))).comp
        (Cochain.ofHom e.inv) (add_zero (-1)) := by
      rw [hn, hi]
      simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
    _ = _ := by
      simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
        Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTrans

/-! 評価した全次数作用の可換性から、加群値 dg 関手の全 Hom 自然性を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (A : Type v) [DGCategory R A] [Small.{u} A]
  (B : Type w) [DGCategory R B] (F H : DGFunctor R B (RightModule R A))
  (a : ∀ Y, ForgetEnrichment.of (Complex R) (F.obj Y) ⟶
    ForgetEnrichment.of (Complex R) (H.obj Y))

lemma dgGluingModuleFunctor_naturality_of_apply
    (h : ∀ (X : A) (Y Z : B) (p q n : ℤ) (hn : q + p = n)
      (g : (homObject R B Y Z).X p) (t : ((F.obj Y).obj (op X)).X q),
      ((moduleEvaluation R A X).map (a Z)).f n
          (((moduleHomπ R A (F.obj Y) (F.obj Z) X).f p
            ((F.map Y Z).f p g)).v q n hn t) =
      ((moduleHomπ R A (H.obj Y) (H.obj Z) X).f p
        ((H.map Y Z).f p g)).v q n hn
        (((moduleEvaluation R A X).map (a Y)).f q t)) (Y Z : B) :
    F.map Y Z ≫ moduleHomPostcompose R A (F.obj Y) (F.obj Z) (H.obj Z) (a Z) =
    H.map Y Z ≫ moduleHomPrecompose R A (F.obj Y) (H.obj Y) (H.obj Z) (a Y) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (moduleHomPostcompose R A (F.obj Y) (F.obj Z) (H.obj Z) (a Z)).f p
      ((F.map Y Z).f p g) =
    (moduleHomPrecompose R A (F.obj Y) (H.obj Y) (H.obj Z) (a Y)).f p
      ((H.map Y Z).f p g)
  apply moduleHomElement_ext R A
  intro X
  erw [moduleHomWhiskerLeft_apply_π, moduleHomWhiskerRight_apply_π]
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact h X Y Z p q n hn g t

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

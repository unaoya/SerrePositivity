module
public import SerrePositivity.DifferentialGraded.Module.LeftMorphisms
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 全Hom自然な成分族から左dg加群の閉零射を構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma leftFamily_rightOpposite_naturality {M N : LeftModule A D}
    (a : ∀ x, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖᵒᵖ) :
    M.toRightOpposite.map x y ≫ homPostcompose (M.toRightOpposite.obj x) (a y.unop.unop) =
      N.toRightOpposite.map x y ≫ homPrecompose (a x.unop.unop) (N.toRightOpposite.obj y) := by
  change (𝟙 _ ≫ M.map x.unop.unop y.unop.unop) ≫
    homPostcompose (M.obj x.unop.unop) (a y.unop.unop) =
    (𝟙 _ ≫ N.map x.unop.unop y.unop.unop) ≫
      homPrecompose (a x.unop.unop) (N.obj y.unop.unop)
  simpa only [Category.id_comp] using h x.unop.unop y.unop.unop

variable [Small.{u} D]

/-- 全次数自然な成分族から、既存の左加群Hom endの閉零射を作る。 -/
def leftModuleMorphismMk {M N : LeftModule A D}
    (a : ∀ x, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N :=
  ForgetEnrichment.homOf (Complex A)
    (ForgetEnrichment.homTo (Complex A)
      (moduleMorphismMk A Dᵒᵖ (M := M.toRightOpposite) (N := N.toRightOpposite)
        (fun x => a x.unop.unop) (leftFamily_rightOpposite_naturality A D a h)))

@[simp]
lemma leftModuleMorphismMk_eval {M N : LeftModule A D} (a) (h) (x : D) :
    (leftModuleEvaluation A D x).map (leftModuleMorphismMk A D (M := M) (N := N) a h) =
      a x := by
  change (moduleEvaluation A Dᵒᵖ (op x)).map
    (moduleMorphismMk A Dᵒᵖ (M := M.toRightOpposite) (N := N.toRightOpposite)
      (fun z => a z.unop.unop) (leftFamily_rightOpposite_naturality A D a h)) = a x
  exact moduleMorphismMk_eval A Dᵒᵖ _ _ (op x)

lemma leftModuleMorphism_ext {M N : LeftModuleCategory A D} {f g : M ⟶ N}
    (h : ∀ x, (leftModuleEvaluation A D x).map f = (leftModuleEvaluation A D x).map g) :
    f = g := by
  change ForgetEnrichment.homTo (Complex A) f = ForgetEnrichment.homTo (Complex A) g
  apply moduleHom_ext
  intro x
  exact (complexClosedHomEquiv A _ _).injective (h x.unop)

end SerrePositivity.DifferentialGraded

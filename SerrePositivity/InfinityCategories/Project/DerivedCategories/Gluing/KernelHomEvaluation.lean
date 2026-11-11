module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomCochain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeBottomAction

/-! kernel 作用を Yoneda 評価し、元の双加群作用と列比較の逆によって表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 通常 tensor 上の右 Hom 作用を評価すると、元の右作用の列同型による移送になる。 -/
lemma dgGluingKernelHomAction_evaluate :
    yonedaHom R D X.right Y.right ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X (representable R Y.right) ≫
      (dgYonedaIso R X.left
        ((Morita.kernelTensor R D C M).obj (representable R Y.right))).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y ≫ (moduleEvaluation R C X.left).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C X.left
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
  have he := congrArg (fun a => a ≫ (moduleEvaluation R C X.left).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_yoneda R C D M X Y)
  simp only [Category.assoc] at he
  erw [← hn] at he
  erw [← eHomWhiskerLeft_comp_assoc (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R X.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
    (dgYonedaIso R X.left
      ((Morita.kernelTensor R D C M).obj (representable R Y.right))).hom] at he
  simp only [Iso.hom_inv_id, eHomWhiskerLeft_id, Category.id_comp] at he
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleConeSquareIso
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic

/-!
双加群の列の射の cone を、代表加群の cone の通常 kernel tensor 像と実加群同型で比較する。
閉零射に自然な tensor–Yoneda 単位と、任意 dg 加群値関手の実 cone 保存を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 同じ通常 kernel の代表加群上の値と元の双加群の列との実同型。 -/
def dgGluingKernelColumnIso (d : ClosedCategory R D) :
    (Morita.kernelTensor R D C M).onClosed.obj ((dgYoneda R D).onClosed.obj d) ≅
      M.toFunctor.onClosed.obj d :=
  (Morita.criterionPerfYonedaTensorIso R D C M).app d

/-- 列の実同型は、元の閉零射に対して自然。 -/
lemma dgGluingKernelColumnIso_naturality {d d' : ClosedCategory R D} (f : d ⟶ d') :
    (Morita.kernelTensor R D C M).onClosed.map ((dgYoneda R D).onClosed.map f) ≫
      (dgGluingKernelColumnIso R C D M d').hom =
    (dgGluingKernelColumnIso R C D M d).hom ≫ M.toFunctor.onClosed.map f :=
  (Morita.criterionPerfYonedaTensorIso R D C M).hom.naturality f

variable {d d' : ClosedCategory R D} (f : d ⟶ d')

/-- tensor–Yoneda の実正方形が誘導する、同じ二つの cone の実同型。 -/
def dgGluingKernelConeSquareIso :
    moduleCone R C ((Morita.kernelTensor R D C M).onClosed.map
      ((dgYoneda R D).onClosed.map f)) ≅
    moduleCone R C (M.toFunctor.onClosed.map f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleConeSquareIso R C _ _
    (dgGluingKernelColumnIso R C D M d) (dgGluingKernelColumnIso R C D M d')
    (dgGluingKernelColumnIso_naturality R C D M f)

/-- 元の双加群像の cone を、代表加群の cone の同じ通常 tensor 像へ送る実同型。 -/
def dgGluingKernelConeIso :
    moduleCone R C (M.toFunctor.onClosed.map f) ≅
      (Morita.kernelTensor R D C M).onClosed.obj
        (moduleCone R D ((dgYoneda R D).onClosed.map f)) :=
  (dgGluingKernelConeSquareIso R C D M f).symm ≪≫
    DifferentialGraded.dgModuleFunctorConeIso R D C (Morita.kernelTensor R D C M)
      ((dgYoneda R D).onClosed.map f)

/-- cone 同型は元の右包含も同じ tensor–Yoneda 単位によって回収する。 -/
lemma dgGluingKernelConeIso_inr :
    moduleConeInr R C (M.toFunctor.onClosed.map f) ≫
      (dgGluingKernelConeIso R C D M f).hom =
    (dgGluingKernelColumnIso R C D M d').inv ≫
      (Morita.kernelTensor R D C M).onClosed.map
        (moduleConeInr R D ((dgYoneda R D).onClosed.map f)) := by
  simp only [dgGluingKernelConeIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [dgGluingKernelConeSquareIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleConeSquareIso_inv_inr, Category.assoc]
  exact congrArg (fun t ↦ (dgGluingKernelColumnIso R C D M d').inv ≫ t)
    (DifferentialGraded.dgModuleFunctorConeComparison_inr R D C
      (Morita.kernelTensor R D C M) ((dgYoneda R D).onClosed.map f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

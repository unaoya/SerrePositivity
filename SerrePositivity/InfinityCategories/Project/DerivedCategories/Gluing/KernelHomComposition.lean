module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomAction

/-! kernel 作用と全整数次数の合成の整合性。円錐の次数 −1 の包含にも適用する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 右加群の全 Hom 合成に関する kernel 作用の豊穣自然性。 -/
lemma dgGluingKernelHomAction_comp (N N' : RightModule R D) :
    eComp (Complex R) (representable R X.right) N N' ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N' =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N ⊗ₘ (Morita.kernelTensor R D C M).map N N') ≫
      eComp (Complex R) (representable R X.left)
        ((Morita.kernelTensor R D C M).obj N) ((Morita.kernelTensor R D C M).obj N') := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction]
  rw [← Category.assoc,
    (Morita.kernelTensor R D C M).map_comp (representable R X.right) N N', Category.assoc]
  erw [eComp_eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M X)
    (ForgetEnrichment.of (Complex R) ((Morita.kernelTensor R D C M).obj N))
    (ForgetEnrichment.of (Complex R) ((Morita.kernelTensor R D C M).obj N'))]
  rw [← Category.assoc]
  erw [tensorHom_comp_whiskerRight]
  rfl

/-- 同じ作用は、任意整数次数の通常順の合成も保存する。 -/
lemma dgGluingKernelHomAction_compose {N N' : RightModule R D} {p q n : ℤ}
    (g : (moduleHom R D N N').X p)
    (t : (moduleHom R D (representable R X.right) N).X q) (hn : q + p = n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N').f n
      (compose R (x := representable R X.right) (y := N) (z := N') g t hn) =
      compose R (x := representable R X.left)
        (y := (Morita.kernelTensor R D C M).obj N)
        (z := (Morita.kernelTensor R D C M).obj N')
        ((Morita.kernelTensor R D C M).map N N' |>.f p g)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N).f q t) hn := by
  have he := congrArg (fun a => a.f n
    (ιTensorObj (moduleHom R D (representable R X.right) N) (moduleHom R D N N')
      q p n hn (t ⊗ₜ[R] g))) (dgGluingKernelHomAction_comp R C D M X N N')
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N').f n
    (forward R (x := representable R X.right) (y := N) (z := N') t g hn) =
    (eComp (Complex R) (representable R X.left) ((Morita.kernelTensor R D C M).obj N)
      ((Morita.kernelTensor R D C M).obj N')).f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X N ⊗ₘ
          (Morita.kernelTensor R D C M).map N N').f n
            (ιTensorObj (moduleHom R D (representable R X.right) N) (moduleHom R D N N')
              q p n hn (t ⊗ₜ[R] g))) at he
  erw [tensorMap_apply] at he
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun a => (q * p).negOnePow • a) he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

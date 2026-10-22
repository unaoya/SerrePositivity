module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelPrimitives

/-! 双加群値 comma から通常 kernel の加群 comma への、全 Hom 鎖同型を持つ実 dg 関手。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "F" => Morita.kernelTensor R D C M
variable (X Y Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "KX" => dgGluingCommaKernelObject R C D M X
local notation "KY" => dgGluingCommaKernelObject R C D M Y
local notation "KZ" => dgGluingCommaKernelObject R C D M Z

omit Z in
/-- 任意パラメータからの第三 cochain は、同じ係数列同型の像。 -/
lemma dgGluingCommaKernelHomComparison (P : Complex R)
    (f : P ⟶ dgFunctorCommaHomComplex R D (RightModule R C) M.toFunctor X Y) :
    dgFunctorCommaHomComparison R (RightModule R D) (RightModule R C) F KX KY P
      (f ≫ (dgGluingCommaKernelHomIso R C D M X Y).hom) =
    (dgFunctorCommaHomComparison R D (RightModule R C) M.toFunctor X Y P f).comp
      (Cochain.ofHom (dgGluingCommaKernelTargetIso R C D M X Y).hom) (add_zero (-1)) := by
  unfold dgFunctorCommaHomComparison
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  change (Cochain.ofHom f).comp
    ((Cochain.ofHom (dgGluingCommaKernelHomIso R C D M X Y).hom).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX KY)
      (zero_add (-1))) (zero_add (-1)) = _
  rw [dgGluingCommaKernelHomIso_primitive,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

omit Y Z in
/-- 元の同じ閉単位を kernel comma の閉単位へ送る。 -/
lemma dgGluingCommaKernelHomIso_identity :
    dgFunctorCommaIdentity R D (RightModule R C) M.toFunctor X ≫
      (dgGluingCommaKernelHomIso R C D M X X).hom =
    dgFunctorCommaIdentity R (RightModule R D) (RightModule R C) F KX := by
  apply dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F KX KX _
  · rw [Category.assoc, dgGluingCommaKernelHomIso_source, ← Category.assoc,
      dgFunctorCommaIdentity_source, dgFunctorCommaIdentity_source]
    exact (dgYoneda R D).map_id X.source
  · rw [Category.assoc, dgGluingCommaKernelHomIso_replacement,
      dgFunctorCommaIdentity_replacement, dgFunctorCommaIdentity_replacement]
    rfl
  · rw [dgGluingCommaKernelHomComparison, dgFunctorCommaIdentity_comparison,
      Cochain.zero_comp, dgFunctorCommaIdentity_comparison]

/-- 全次数の合成を、二射影と同じ二項の第三 cochain ごと保存する。 -/
lemma dgGluingCommaKernelHomIso_composition :
    dgFunctorCommaComposition R D (RightModule R C) M.toFunctor X Y Z ≫
      (dgGluingCommaKernelHomIso R C D M X Z).hom =
    ((dgGluingCommaKernelHomIso R C D M X Y).hom ⊗ₘ
      (dgGluingCommaKernelHomIso R C D M Y Z).hom) ≫
      dgFunctorCommaComposition R (RightModule R D) (RightModule R C) F KX KY KZ := by
  apply dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F KX KZ _
  · rw [Category.assoc, dgGluingCommaKernelHomIso_source, ← Category.assoc,
      dgFunctorCommaComposition_source, Category.assoc, dgFunctorCommaComposition_source]
    simp only [dgFunctorCommaSourceComposite, ← Category.assoc, tensorHom_comp_tensorHom,
      dgGluingCommaKernelHomIso_source]
    have he := congrArg (fun k =>
      (dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor X Y ⊗ₘ
        dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor Y Z) ≫ k)
      ((dgYoneda R D).map_comp X.source Y.source Z.source)
    simpa only [← Category.assoc, tensorHom_comp_tensorHom] using! he
  · rw [Category.assoc, dgGluingCommaKernelHomIso_replacement,
      dgFunctorCommaComposition_replacement, Category.assoc,
      dgFunctorCommaComposition_replacement]
    simp only [dgFunctorCommaReplacementComposite, ← Category.assoc,
      tensorHom_comp_tensorHom, dgGluingCommaKernelHomIso_replacement]
    rfl
  · rw [dgGluingCommaKernelHomComparison, dgFunctorCommaComposition_comparison,
      dgFunctorCommaHomComparison_precompose, dgFunctorCommaComposition_comparison,
      dgGluingCommaKernelCompositePrimitive]

omit X Y Z in
/-- 右 Yoneda と tensor–Yoneda の列同型により得る実 dg 関手。 -/
def dgGluingCommaToKernel :
    DGFunctor R (DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
      (DGFunctorCommaObject R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)) where
  obj := dgGluingCommaKernelObject R C D M
  map X Y := (dgGluingCommaKernelHomIso R C D M X Y).hom
  map_id := dgGluingCommaKernelHomIso_identity R C D M
  map_comp := dgGluingCommaKernelHomIso_composition R C D M

end SerrePositivity.InfinityCategories

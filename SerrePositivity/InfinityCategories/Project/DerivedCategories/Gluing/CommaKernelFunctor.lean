module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaKernelPrimitives

/-! 双加群値 comma から通常 kernel の加群 comma への、全 Hom 鎖同型を持つ実 dg 関手。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "F" => Morita.kernelTensor R D C M
variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M X
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M Y
local notation "KZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M Z

omit Z in
/-- 任意パラメータからの第三 cochain は、同じ係数列同型の像。 -/
lemma dgGluingCommaKernelHomComparison (P : Complex R)
    (f : P ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R D (RightModule R C) M.toFunctor X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R (RightModule R D) (RightModule R C) F KX KY P
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Y).hom) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R D (RightModule R C) M.toFunctor X Y P f).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M X Y).hom) (add_zero (-1)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  change (Cochain.ofHom f).comp
    ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Y).hom).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX KY)
      (zero_add (-1))) (zero_add (-1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_primitive,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

omit Y Z in
/-- 元の同じ閉単位を kernel comma の閉単位へ送る。 -/
lemma dgGluingCommaKernelHomIso_identity :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R D (RightModule R C) M.toFunctor X ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X X).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R (RightModule R D) (RightModule R C) F KX := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F KX KX _
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_source, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source]
    exact (dgYoneda R D).map_id X.source
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement]
    rfl
  · rw [dgGluingCommaKernelHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison,
      Cochain.zero_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison]

/-- 全次数の合成を、二射影と同じ二項の第三 cochain ごと保存する。 -/
lemma dgGluingCommaKernelHomIso_composition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R D (RightModule R C) M.toFunctor X Y Z ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Z).hom =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Y).hom ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M Y Z).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R (RightModule R D) (RightModule R C) F KX KY KZ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F KX KZ _
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_source, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite, ← Category.assoc, tensorHom_comp_tensorHom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_source]
    have he := congrArg (fun k =>
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor Y Z) ≫ k)
      ((dgYoneda R D).map_comp X.source Y.source Z.source)
    simpa only [← Category.assoc, tensorHom_comp_tensorHom] using! he
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite, ← Category.assoc,
      tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_replacement]
    rfl
  · rw [dgGluingCommaKernelHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelCompositePrimitive]

omit X Y Z in
/-- 右 Yoneda と tensor–Yoneda の列同型により得る実 dg 関手。 -/
def dgGluingCommaToKernel :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M
  map X Y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Y).hom
  map_id := dgGluingCommaKernelHomIso_identity R C D M
  map_comp := dgGluingCommaKernelHomIso_composition R C D M

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

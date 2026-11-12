module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaImageCompositePrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaProjections

/-! 任意関手の comma を、二射影・比較 cochain・全 dg 合成を保って標的恒等 comma へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Y
local notation "IZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Z
local notation "aXY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y
local notation "aYZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F Y Z
local notation "aXZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Z

omit Y Z in
lemma dgGluingCommaImageHomMap_identity :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R C E F X ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity R E E (DGFunctor.id E) IX := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R E E (DGFunctor.id E) IX IX _
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_source,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_source]
    rfl
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_replacement]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison]

lemma dgGluingCommaImageHomMap_composition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z ≫ aXZ =
      (aXY ⊗ₘ aYZ) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R E E (DGFunctor.id E) IX IZ _
  · have hl : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z ≫ aXZ) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IZ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite R C E F X Y Z ≫ F.map X.source Z.source := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source]
    have hr : ((aXY ⊗ₘ aYZ) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IZ =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z) ≫
        eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite, ← Category.assoc, tensorHom_comp_tensorHom,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_source]
      rfl
    exact hl.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite_image R C E F X Y Z).trans hr.symm)
  · have hl : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z ≫ aXZ) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IZ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite R C E F X Y Z := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_replacement,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement]
    have hr : ((aXY ⊗ₘ aYZ) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R E E (DGFunctor.id E) IX IY IZ) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IZ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite R C E F X Y Z := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite, ← Category.assoc, tensorHom_comp_tensorHom,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_replacement]
      rfl
    exact hl.trans hr.symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageCompositePrimitive]

omit X Y Z in
def dgGluingCommaImageFunctor : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F
  map_id := dgGluingCommaImageHomMap_identity R C E F
  map_comp := dgGluingCommaImageHomMap_composition R C E F

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

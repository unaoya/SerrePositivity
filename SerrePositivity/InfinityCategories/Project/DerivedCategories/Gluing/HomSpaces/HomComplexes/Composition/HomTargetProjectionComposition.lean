module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetPrimitiveComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Composition
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCommaElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.CommaPrimitiveActions
/-!
概要：元終域の comma Hom 比較は左右射影上で全次数の合成を保持する。
方針：元の左右射影関手と comma の射影関手の合成保存を、厳密な成分回収で照合する。
規約：元の二関手と全整数次数を保持する。
使われ方：第三 cochain の合成式と合わせ、実 dg 比較関手を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
variable [Small.{u} E]
lemma dgGluingHomTargetCommaHomMap_forward_source {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      (forward R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)
        (z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_source_element]
  have ht := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D E q)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D E q _ _).f (r + s) _ = _ at ht
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_source_element R C D E p q X Y r a
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_source_element R C D E p q Y Z s b
  have hf := congrArg₂ (fun
      (a' : GradedHom R (X.right) (Y.right) r)
      (b' : GradedHom R (Y.right) (Z.right) s) =>
    forward R a' b' rfl) ha hb
  have hs := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) a b rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at hs
  exact hs.trans (ht.trans hf).symm
lemma dgGluingHomTargetCommaHomMap_forward_replacement {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      (forward R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)
        (z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement_element]
  have ht := DGFunctor.map_forward R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D E q)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D E q _ _).f (r + s) _ = _ at ht
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement_element R C D E p q X Y r a
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement_element R C D E p q Y Z s b
  have hf := congrArg₂ (fun
      (a' : GradedHom R (p.obj X.left) (p.obj Y.left) r)
      (b' : GradedHom R (p.obj Y.left) (p.obj Z.left) s) =>
    forward R a' b' rfl) ha hb
  have hs := DGFunctor.map_forward R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp
      p) a b rfl
  exact hs.trans (ht.trans hf).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

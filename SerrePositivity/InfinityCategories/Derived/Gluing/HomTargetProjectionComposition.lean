module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetPrimitiveComposition
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.Composition
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrimitiveActions
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
variable [Small.{u} E]
lemma dgGluingHomTargetCommaHomMap_forward_source {r s : ℤ}
    (a : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgFunctorCommaSourceHomMap R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      ((dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (dgFunctorCommaSourceHomMap R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      (forward R (x := dgGluingHomTargetCommaObject R C D E p q X)
        (y := dgGluingHomTargetCommaObject R C D E p q Y)
        (z := dgGluingHomTargetCommaObject R C D E p q Z)
        ((dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [dgGluingHomTargetCommaHomMap_source_element]
  have ht := DGFunctor.map_forward R (dgFunctorCommaSource R D E q)
    ((dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
    ((dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl
  change (dgFunctorCommaSourceHomMap R D E q _ _).f (r + s) _ = _ at ht
  have ha := dgGluingHomTargetCommaHomMap_source_element R C D E p q X Y r a
  have hb := dgGluingHomTargetCommaHomMap_source_element R C D E p q Y Z s b
  have hf := congrArg₂ (fun
      (a' : GradedHom R (X.right) (Y.right) r)
      (b' : GradedHom R (Y.right) (Z.right) s) =>
    forward R a' b' rfl) ha hb
  have hs := DGFunctor.map_forward R (dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) a b rfl
  rw [dgGluingRight_map, dgGluingRight_map, dgGluingRight_map] at hs
  exact hs.trans (ht.trans hf).symm
lemma dgGluingHomTargetCommaHomMap_forward_replacement {r s : ℤ}
    (a : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgFunctorCommaReplacementHomMap R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      ((dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (dgFunctorCommaReplacementHomMap R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).f (r + s)
      (forward R (x := dgGluingHomTargetCommaObject R C D E p q X)
        (y := dgGluingHomTargetCommaObject R C D E p q Y)
        (z := dgGluingHomTargetCommaObject R C D E p q Z)
        ((dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [dgGluingHomTargetCommaHomMap_replacement_element]
  have ht := DGFunctor.map_forward R (dgFunctorCommaReplacement R D E q)
    ((dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
    ((dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl
  change (dgFunctorCommaReplacementHomMap R D E q _ _).f (r + s) _ = _ at ht
  have ha := dgGluingHomTargetCommaHomMap_replacement_element R C D E p q X Y r a
  have hb := dgGluingHomTargetCommaHomMap_replacement_element R C D E p q Y Z s b
  have hf := congrArg₂ (fun
      (a' : GradedHom R (p.obj X.left) (p.obj Y.left) r)
      (b' : GradedHom R (p.obj Y.left) (p.obj Z.left) s) =>
    forward R a' b' rfl) ha hb
  have hs := DGFunctor.map_forward R ((dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp
      p) a b rfl
  exact hs.trans (ht.trans hf).symm
end SerrePositivity.InfinityCategories

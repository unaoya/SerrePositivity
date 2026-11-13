module
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCommaElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.CommaPrimitiveActions
/-!
概要：Hom gluing の第三成分の合成を、元の共通終域の二つの合成で表示する。
方針：元双加群の作用公式へ戻し、後合成の二つの Koszul 符号を相殺する。
規約：全整数次数と元の二関手を保持する。
使われ方：元終域への comma 比較の合成保存に用いる。
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
lemma dgGluingHomTargetPrimitive_forward {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Z).v
      (r + s) (r + s - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) a b rfl) =
    forward R (x := p.obj X.left) (y := q.obj Y.right) (z := q.obj Z.right)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y).v
        r (r - 1) (by omega) a)
      ((q.map Y.right Z.right).f s
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) Y Z).f s b))
      (by omega) +
    r.negOnePow • forward R (x := p.obj X.left) (y := p.obj Y.left) (z := q.obj Z.right)
      ((p.map X.left Y.left).f r
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y).f r a))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) Y Z).v
        s (s - 1) (by omega) b) (by omega) := by
  rw [dgHomGluingPrimitive_forward]
  erw [dgHomGluingBimodule_leftAction, dgHomGluingBimodule_rightAction]
  erw [Int.mul_comm s (r - 1), smul_smul, Int.units_mul_self, one_smul]
variable [Small.{u} E]
lemma dgGluingHomTargetCommaHomMap_forward_primitive {r s : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).v
      (r + s) (r + s - 1) (by omega)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)).v
      (r + s) (r + s - 1) (by omega)
      (forward R
        (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)
        (z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Z)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_primitive_element,
    dgGluingHomTargetPrimitive_forward, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaForward_primitive,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_primitive_element,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_primitive_element,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_image_element,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement_element]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

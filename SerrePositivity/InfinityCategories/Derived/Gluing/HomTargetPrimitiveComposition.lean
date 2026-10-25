module
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrimitiveActions
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y Z : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
lemma dgGluingHomTargetPrimitive_forward {r s : ℤ}
    (a : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Z).v
      (r + s) (r + s - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) a b rfl) =
    forward R (x := p.obj X.left) (y := q.obj Y.right) (z := q.obj Z.right)
      ((dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y).v
        r (r - 1) (by omega) a)
      ((q.map Y.right Z.right).f s
        ((dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) Y Z).f s b))
      (by omega) +
    r.negOnePow • forward R (x := p.obj X.left) (y := p.obj Y.left) (z := q.obj Z.right)
      ((p.map X.left Y.left).f r
        ((dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y).f r a))
      ((dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) Y Z).v
        s (s - 1) (by omega) b) (by omega) := by
  rw [dgHomGluingPrimitive_forward]
  erw [dgHomGluingBimodule_leftAction, dgHomGluingBimodule_rightAction]
  erw [Int.mul_comm s (r - 1), smul_smul, Int.units_mul_self, one_smul]
variable [Small.{u} E]
lemma dgGluingHomTargetCommaHomMap_forward_primitive {r s : ℤ}
    (a : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X r)
    (b : (dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) Y Z).X s) :
    (dgFunctorCommaPrimitive R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).v
      (r + s) (r + s - 1) (by omega)
      ((dgGluingHomTargetCommaHomMap R C D E p q X Z).f (r + s)
        (forward R (x := X) (y := Y) (z := Z) a b rfl)) =
    (dgFunctorCommaPrimitive R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Z)).v
      (r + s) (r + s - 1) (by omega)
      (forward R
        (x := dgGluingHomTargetCommaObject R C D E p q X)
        (y := dgGluingHomTargetCommaObject R C D E p q Y)
        (z := dgGluingHomTargetCommaObject R C D E p q Z)
        ((dgGluingHomTargetCommaHomMap R C D E p q X Y).f r a)
        ((dgGluingHomTargetCommaHomMap R C D E p q Y Z).f s b) rfl) := by
  rw [dgGluingHomTargetCommaHomMap_primitive_element,
    dgGluingHomTargetPrimitive_forward, dgGluingCommaForward_primitive,
    dgGluingHomTargetCommaHomMap_primitive_element,
    dgGluingHomTargetCommaHomMap_primitive_element,
    dgGluingHomTargetCommaHomMap_image_element,
    dgGluingHomTargetCommaHomMap_replacement_element]
end SerrePositivity.InfinityCategories

module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetCone
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeDifferential
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveDifferential

/-! # 元の gluing Hom の三成分を実 Yoneda Hom へ送る
概要：左右の実鎖射影と第三 cochain を、同じ表現可能加群の Hom に移す。
方針：元の二関手と Yoneda の全 Hom 写像を合成する。
規約：第三成分と対象の元の閉比較を保持。使われ方：実 cone Hom 鎖写像。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 左射影と元の左関手・Yoneda を合成した実 Hom 鎖写像。 -/
def dgHomGluingConeLeftMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y ⟶
      moduleHom R E (representable R (p.obj X.left)) (representable R (p.obj Y.left)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D _ X Y ≫ p.map X.left Y.left ≫
    (dgYoneda R E).map (p.obj X.left) (p.obj Y.left)

/-- 右射影と元の右関手・Yoneda を合成した実 Hom 鎖写像。 -/
def dgHomGluingConeRightMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y ⟶
      moduleHom R E (representable R (q.obj X.right)) (representable R (q.obj Y.right)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D _ X Y ≫ q.map X.right Y.right ≫
    (dgYoneda R E).map (q.obj X.right) (q.obj Y.right)

/-- 第三比較を同じ Yoneda Hom へ移した実次数 −1 cochain。 -/
def dgHomGluingConePrimitive :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y)
      (moduleHom R E (representable R (p.obj X.left))
        (representable R (q.obj Y.right))) (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y).comp
    (Cochain.ofHom ((dgYoneda R E).map (p.obj X.left) (q.obj Y.right))) (add_zero (-1))

/-- 同じ実 cone 比較射の閉元は、元の gluing 閉元の Yoneda 像。 -/
lemma dgHomGluingTargetModuleMap_cycle :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgHomGluingTargetModuleMap R C D E p q X))).val =
      ((dgYoneda R E).map (p.obj X.left) (q.obj X.right)).f 0 X.gluing.val := by
  change (closedHomEquiv R (RightModule R E) _ _
    ((dgYoneda R E).onClosed.map (dgHomGluingTargetMap R C D E p q X))).val = _
  rw [DGFunctor.closedHomEquiv_map]
  change ((dgYoneda R E).map _ _).f 0
    ((closedHomEquiv R E _ _)
      ((closedHomEquiv R E _ _).symm X.gluing)).val = _
  exact congrArg (fun t => ((dgYoneda R E).map _ _).f 0 t.val)
    ((closedHomEquiv R E _ _).apply_symm_apply X.gluing)

end SerrePositivity.KST.SConstruction

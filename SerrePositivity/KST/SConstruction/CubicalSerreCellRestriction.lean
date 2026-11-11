module
public import SerrePositivity.KST.SConstruction.CubicalSerreGenerators

/-! # 元の cell の制限と Serre 鎖射の関係
概要：元の具体的立方体射による cell の制限を、元の Yoneda 射と鎖射で回収する。
方針：同じ Yoneda 同値と左 Kan 延長の単位の自然性を使う。
規約：全ての元の cell と座標を保つ。使われ方：Day tensor の二つの cell の鎖比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

/-- 元の cell の制限は、元の Yoneda 射の前合成。 -/
lemma cubicalCell_restrict {K : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ d) (x : K.obj (op d)) :
    cubicalYoneda.map f ≫ cubicalCell d x = cubicalCell c (K.map f.op x) := by
  change uliftYoneda.{u}.map f ≫ uliftYonedaEquiv.symm x =
    uliftYonedaEquiv.symm (K.map f.op x)
  exact (uliftYonedaEquiv_symm_map.{u} f.op x).symm

/-- 元の恒等 cell の Yoneda 射は恒等自然変換。 -/
lemma cubicalCell_identity (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalCell c (K := cubicalYoneda.{u}.obj c) (ULift.up (𝟙 c)) =
      𝟙 (cubicalYoneda.obj c) := by
  apply (uliftYonedaEquiv.{u} (X := c) (F := cubicalYoneda.{u}.obj c)).injective
  change (uliftYonedaEquiv.{u} (X := c) (F := cubicalYoneda.{u}.obj c))
    ((uliftYonedaEquiv.{u} (X := c) (F := cubicalYoneda.{u}.obj c)).symm
      (ULift.up (𝟙 c))) = ULift.up (𝟙 c)
  exact Equiv.apply_symm_apply _ _

/-- 元の恒等 cell の鎖射は、同じ左 Kan 延長の単位。 -/
lemma cubicalSerreCell_identity (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalSerreCell A c (K := cubicalYoneda.obj c) (ULift.up (𝟙 c)) =
      (cubicalSerreChainsCubeUnit A).app c := by
  change cubicalSerreGenerator A
    (cubicalCell c (K := cubicalYoneda.{u}.obj c) (ULift.up (𝟙 c))) = _
  rw [cubicalCell_identity, cubicalSerreGenerator_id]

/-- 元の cell の制限は、元の Serre 鎖射との合成を回収する。 -/
lemma cubicalSerreCell_restrict {K : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ d) (x : K.obj (op d)) :
    (serreConcreteCubeComplexFunctor A).map f ≫ cubicalSerreCell A d x =
      cubicalSerreCell A c (K.map f.op x) := by
  have h := cubicalSerreGenerator_relation A f (cubicalCell d x)
  rw [cubicalCell_restrict f x] at h
  exact h

end SerrePositivity.KST.SConstruction

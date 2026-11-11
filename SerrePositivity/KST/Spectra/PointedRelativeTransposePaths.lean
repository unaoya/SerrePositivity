module

public import SerrePositivity.KST.Spectra.PointedBasedPathClosed
public import SerrePositivity.KST.Spectra.PointedTransposeRestrictions
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality
public import SerrePositivity.KST.Spectra.LoopMappingOperations

/-!
概要：元の区間族の部分パラメータへの制限を、転置後の指定射影への垂直性へ移す。
方針：内部 Hom の交換と制限の厳密正方形を使う。零境界では基点固定から全区間の定数性を得る。
規約：端点の一致だけから垂直性を推論しない。使われ方：基点つき球面族の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 元の零族の転置も、同じ Hom の零族。 -/
lemma transpose_zero (A U V : PointedSimplicialSet.{u}) :
    transpose (0 : A ⟶ (ihom U).obj V) = 0 := by
  apply (familyVertexEquiv U ((ihom A).obj V)).injective
  change familyVertex (transpose (0 : A ⟶ (ihom U).obj V)) =
    familyVertex (0 : U ⟶ (ihom A).obj V)
  rw [familyVertex_transpose, familyVertex_zero, familyVertex_zero]
  exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom

/-- 外側のパラメータへの前合成を転置すると、内側の同じ源への制限になる。 -/
lemma transpose_pre_outer {A B U V : PointedSimplicialSet.{u}}
    (f : A ⟶ (ihom U).obj V) (j : B ⟶ A) :
    transpose (j ≫ f) = transpose f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V := by
  have h := congrArg transpose (transpose_pre_inner (transpose f) j)
  simp only [transpose_transpose] at h
  exact h.symm

namespace VerticalPath

/-- 元の区間の部分パラメータへの制限が定数なら、同じ区間の転置は制限射影の上で垂直。 -/
def transposeOver {A B U V : PointedSimplicialSet.{u}} {f g : A ⟶ (ihom U).obj V}
    (H : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g) (j : B ⟶ A)
    (hrel : H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right =
      SSet.const (familyVertex (j ≫ f))) :
    VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) (transpose f) (transpose g) where
  path := H.basedTranspose.path
  zero := H.basedTranspose.zero
  one := H.basedTranspose.one
  «over» := by
    have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left j U V
    simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
    have hs' := congrArg Under.Hom.right hs.symm
    change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right ≫
        (PointedObject.basedHomMap U (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V)).right =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B U V).hom.right at hs'
    change (H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right) ≫ _ = _
    rw [Category.assoc, hs', ← Category.assoc, hrel, SSet.const_comp]
    exact congrArg SSet.const ((familyVertex_transpose (j ≫ f)).symm.trans
      (congrArg familyVertex (transpose_pre_outer f j)))

/-- 転置して射影を指定しても、元の転置区間そのものを保持する。 -/
lemma transposeOver_homotopy_h {A B U V : PointedSimplicialSet.{u}}
    {f g : A ⟶ (ihom U).obj V}
    (H : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g) (j : B ⟶ A)
    (hrel : H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right =
      SSet.const (familyVertex (j ≫ f))) :
    (H.transposeOver j hrel).homotopy.h = H.basedTranspose.homotopy.h := by
  rw [homotopy_h, homotopy_h]
  rfl

/-- 部分パラメータ上で入力が零なら、元の基点固定区間の全区間もその部分で定数。 -/
lemma pre_zero_boundary {S A B E : PointedSimplicialSet.{u}} {f g : S ⟶ E}
    (H : VerticalPath (PointedObject.toPoint E) f g) (e : A ⟶ S) (j : B ⟶ A)
    (hzero : j ≫ e = 0) :
    (H.pre e).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = SSet.const (familyVertex (j ≫ (e ≫ f))) := by
  apply (cancel_mono (PointedObject.basedHomι B E)).1
  change (H.pre e).path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E ≫ PointedObject.basedHomι B E = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_const_familyVertex, ← homotopy_h, pre_homotopy_h]
  have hz := congrArg Under.Hom.right hzero
  change j.right ≫ e.right = (0 : B ⟶ S).right at hz
  rw [PointedObject.zero_right] at hz
  rw [← Category.assoc, ← comp_whiskerRight, hz, comp_whiskerRight_assoc, H.homotopy_base]
  have hb : j ≫ (e ≫ f) = 0 := by rw [← Category.assoc, hzero, zero_comp]
  rw [hb, PointedObject.zero_right]
  simp only [comp_toUnit_assoc]

/-- 零境界を持つ元の入力へ前合成した区間を、指定部分への射影を固定して転置する。 -/
def preTransposeOverZero {S A B U V : PointedSimplicialSet.{u}}
    {f g : S ⟶ (ihom U).obj V}
    (H : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g)
    (e : A ⟶ S) (j : B ⟶ A) (hzero : j ≫ e = 0) :
    VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) (transpose (e ≫ f)) (transpose (e ≫ g)) :=
  (H.pre e).transposeOver j (H.pre_zero_boundary e j hzero)

end VerticalPath
end SerrePositivity.KST.Spectra.PointedMapping

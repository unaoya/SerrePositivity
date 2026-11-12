module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessTensorIso

/-!
概要：パラメーターの制限による積上の四角形の前合成と currying の自然性。
方針：底側と全空間側を同じパラメーターの射で前合成する。
規約：高次単体の射として厳密に可換させる。
使われ方：区間族の境界制限との比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：内部 currying はパラメーターでの前合成に自然。
方針：二回 uncurry して結合子と評価の自然性を使う。
規約：任意の単体集合と射。
使われ方：積のパラメーターを境界へ制限する射の比較。 -/
lemma transportIhomCurry_pre_whiskerLeft (A X : SSet.{u}) {K L : SSet.{u}} (i : L ⟶ K) :
    (pre (A ◁ i)).app X ≫ (ihomCurryIso A L X).hom =
      (ihomCurryIso A K X).hom ≫ (pre i).app ((ihom A).obj X) := by
  change (pre (A ◁ i)).app X ≫ ihomCurry A L X = ihomCurry A K X ≫ _
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_ihomCurry, uncurry_ihomCurry]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
  simp only [← Category.assoc]
  rw [associator_inv_naturality_right]
  simp only [Category.assoc, id_tensor_pre_app_comp_ev]
  rw [← Category.assoc, ← associator_inv_naturality_middle]
  rw [Category.assoc]

/-- 概要：積上の四角形をパラメーターの射で制限する。
方針：底側と全空間側を同じ射で前合成する。
規約：表現条件をまだ課さない全四角形のデータ。
使われ方：各頂点での表現条件の検査。 -/
def LeftTransportSquare.tensorPre {E B K L : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ▷ K)) (i : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ▷ L) :=
  ⟨(B ◁ i) ≫ S.diagram, (E ◁ i) ≫ S.pointedMap, by
    rw [Category.assoc, S.comm, ← Category.assoc]
    have h : (E ◁ i) ≫ (p ▷ K) = (p ▷ L) ≫ (B ◁ i) := rfl
    rw [h, Category.assoc]⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (tensorPre)


/-- 概要：積上の四角形全体のパラメーター制限。
方針：両関手空間の前合成を引き戻しへ束ねる。
規約：全高次単体の射として定義する。
使われ方：実際の表現空間のパラメーター制限の周囲の射。 -/
def transportSquareTensorPre {E B : SSet.{u + 1}} (p : E ⟶ B)
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (p ▷ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (p ▷ L) :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K) ≫ (pre (E ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K) ≫ (pre (B ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (by
      rw [Category.assoc, pre_comm_ihom_map, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition, Category.assoc, Category.assoc]
      congr 1)

/-- 概要：四角形のパラメーター制限の全空間側は同じ前合成。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：currying の自然性の第一成分。 -/
lemma transportSquareTensorPre_pointed {E B : SSet.{u + 1}} (p : E ⟶ B)
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportSquareTensorPre p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K) ≫ (pre (E ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity :=
  pullback.lift_fst _ _ _

/-- 概要：四角形のパラメーター制限の分類図式は同じ前合成。
方針：引き戻しへの lift の第二射影。
規約：厳密な射の一致。
使われ方：currying の自然性の第二成分。 -/
lemma transportSquareTensorPre_diagram {E B : SSet.{u + 1}} (p : E ⟶ B)
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportSquareTensorPre p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K) ≫ (pre (B ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

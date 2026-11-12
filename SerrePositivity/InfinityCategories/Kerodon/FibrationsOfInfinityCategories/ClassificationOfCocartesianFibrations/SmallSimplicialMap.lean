module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent

/-!
概要：各次数で小さい単体集合の縮小における射の作用。
方針：全空間の縮小同型で元の射を共役し、宇宙を降ろす。
規約：縮小は恒等射と合成を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の底の射に対する関手性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい代表の間に元の単体集合の射を移す。
方針：縮小同型を両側に合成し、持ち上げた射を降ろす。
規約：X と Y の各次数は u に小さい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい全空間の比較写像。 -/
noncomputable def smallSimplicialMap {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso X).hom ≫ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso Y).inv)

/-- 概要：縮小した射の持ち上げは元の射を縮小同型で共役した射。
方針：射の宇宙を降ろして持ち上げる往復を使う。
規約：元の射 f は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、縮小の比較写像の自然性。 -/
lemma smallSimplicialMap_ulift {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialMap f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso X).hom ≫ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso Y).inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _

/-- 概要：全空間の縮小の同型は射について自然。
方針：縮小した射の計算則に同型の順方向を後合成して往復を消す。
規約：二つの全空間の同型を明示する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の比較四角形。 -/
lemma smallSimplicialMap_naturality {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialMap f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso X).hom ≫ f := by
  rw [smallSimplicialMap_ulift, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 概要：全空間の縮小は恒等射を保つ。
方針：同型の往復を消して宇宙を降ろす。
規約：次数ごとの縮小の選択を固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底の射に関する小さい構成の単位則。 -/
lemma smallSimplicialMap_id (X : SSet.{max u v}) [∀ n, Small.{u} (X.obj n)] :
    smallSimplicialMap.{u, v} (𝟙 X) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet X) := by
  rw [smallSimplicialMap, Category.id_comp, Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_id]

/-- 概要：全空間の縮小は射の合成を保つ。
方針：中間の縮小同型の往復を消し、宇宙を降ろす操作の合成則を使う。
規約：f の後に g を合成する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の底の射に関する合成則。 -/
lemma smallSimplicialMap_comp {X Y Z : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] [∀ n, Small.{u} (Z.obj n)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallSimplicialMap.{u, v} (f ≫ g) = smallSimplicialMap f ≫ smallSimplicialMap g := by
  rw [smallSimplicialMap, smallSimplicialMap, smallSimplicialMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_comp]
  congr 1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

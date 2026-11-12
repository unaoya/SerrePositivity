module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.ProductProjectionPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareTensorPreLaws

/-!
概要：点上の四角形の族の比較は実際の積射影の制限と可換。
方針：底の正規化の自然性と積の currying の自然性を続ける。
規約：全高次の分類図式と全空間の射を厳密に保つ。
使われ方：区間の境界制限を点上の四角形の族の境界へ移す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：積射影の実際の底変換制限を新しい積の全空間へ戻す。
方針：制限に引き戻し全空間の同型による前合成を続ける。
規約：元の二つの射をともに保持する。
使われ方：点上の表現の族の境界制限の周囲の射。 -/
def pointProductSquarePre (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (snd E K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (snd E L) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction (snd E K) i ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre (snd E L) (pullback.snd (snd E K) i)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.productProjectionPullbackIso E i).hom (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.productProjectionPullbackIso_hom_snd E i)

/-- 概要：積射影の制限の全空間側は同じパラメーターの前合成。
方針：二つの射影公式と前合成の合成則を使う。
規約：全高次単体の厳密な等式。
使われ方：全空間側の境界固定条件の回収。 -/
lemma pointProductSquarePre_pointed (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (snd E L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (snd E K) ≫ (pre (E ◁ i)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity := by
  dsimp only [pointProductSquarePre]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_pointed, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_pointed, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.productProjectionPullbackIso_hom_fst]

/-- 概要：積射影の制限の分類図式は底の射の前合成。
方針：底変換と全空間同型の第二射影を使う。
規約：全高次単体の厳密な等式。
使われ方：底側の境界固定条件の回収。 -/
lemma pointProductSquarePre_diagram (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (snd E L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (snd E K) ≫ (pre i).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := by
  dsimp only [pointProductSquarePre]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_diagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_diagram]

/-- 概要：点との積の底の正規化は実際の積射影の制限と可換。
方針：二射影で底の同型の自然性と前合成の合成則を使う。
規約：両側の境界の射を厳密に保持する。
使われ方：内部 currying の自然性へ接続する正方形。 -/
lemma pointProductSquareBasePre_naturality (E : SSet.{u + 1})
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ L)
        (snd E L) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso L).hom rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ K) (snd E K)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso K).hom rfl ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E) i := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ L) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ K) (snd E K)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso K).hom rfl ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E) i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ L)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre_pointed, pointProductSquarePre_pointed,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_pointed, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre_pointed]
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ L) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ K) (snd E K)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso K).hom rfl ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E) i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ L)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre_diagram, ← Category.assoc,
      pointProductSquarePre_diagram]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorPre_diagram,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E ▷ K) (snd E K)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso K).hom rfl), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre_diagram]
    simp only [Category.assoc]
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointTensorIso_naturality]

/-- 概要：点上の四角形の族の同型は実際のパラメーター制限に自然。
方針：底の正規化と内部 currying の二つの自然性を続ける。
規約：任意のパラメーターの射で全高次単体を保持する。
使われ方：区間の実際の境界制限を点上の族の境界制限へ移す。 -/
lemma pointProductSquareTensorIso_hom_naturality (E : SSet.{u + 1})
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointProductSquareTensorIso E L).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointProductSquareTensorIso E K).hom ≫
        (pre i).app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointProductSquareTensorIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBaseIso]
  rw [← Category.assoc, pointProductSquareBasePre_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso_hom_naturality, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

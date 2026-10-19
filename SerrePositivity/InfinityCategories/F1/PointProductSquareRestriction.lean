module

public import SerrePositivity.InfinityCategories.F1.ProductProjectionPullbackIso
public import SerrePositivity.InfinityCategories.F1.TransportSquareTensorPreLaws

/-!
概要：点上の四角形の族の比較は実際の積射影の制限と可換。
方針：底の正規化の自然性と積の currying の自然性を続ける。
規約：全高次の分類図式と全空間の射を厳密に保つ。
使われ方：区間の境界制限を点上の四角形の族の境界へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積射影の実際の底変換制限を新しい積の全空間へ戻す。
方針：制限に引き戻し全空間の同型による前合成を続ける。
規約：元の二つの射をともに保持する。
使われ方：点上の表現の族の境界制限の周囲の射。 -/
def pointProductSquarePre (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportSquareSpace (snd E K) ⟶ transportSquareSpace (snd E L) :=
  transportSquareRestriction (snd E K) i ≫
    transportSquareTotalPre (snd E L) (pullback.snd (snd E K) i)
      (productProjectionPullbackIso E i).hom (productProjectionPullbackIso_hom_snd E i)

/-- 概要：積射影の制限の全空間側は同じパラメーターの前合成。
方針：二つの射影公式と前合成の合成則を使う。
規約：全高次単体の厳密な等式。
使われ方：全空間側の境界固定条件の回収。 -/
lemma pointProductSquarePre_pointed (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ transportSquarePointed (snd E L) =
      transportSquarePointed (snd E K) ≫ (pre (E ◁ i)).app PointedSpaceInfinity := by
  dsimp only [pointProductSquarePre]
  rw [Category.assoc, transportSquareTotalPre_pointed, ← Category.assoc,
    transportSquareRestriction_pointed, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    productProjectionPullbackIso_hom_fst]

/-- 概要：積射影の制限の分類図式は底の射の前合成。
方針：底変換と全空間同型の第二射影を使う。
規約：全高次単体の厳密な等式。
使われ方：底側の境界固定条件の回収。 -/
lemma pointProductSquarePre_diagram (E : SSet.{u + 1}) {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ transportSquareDiagram (snd E L) =
      transportSquareDiagram (snd E K) ≫ (pre i).app SpaceInfinity := by
  dsimp only [pointProductSquarePre]
  rw [Category.assoc, transportSquareTotalPre_diagram, transportSquareRestriction_diagram]

/-- 概要：点との積の底の正規化は実際の積射影の制限と可換。
方針：二射影で底の同型の自然性と前合成の合成則を使う。
規約：両側の境界の射を厳密に保持する。
使われ方：内部 currying の自然性へ接続する正方形。 -/
lemma pointProductSquareBasePre_naturality (E : SSet.{u + 1})
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ transportSquareBasePre (transportPointProjection E ▷ L)
        (snd E L) (transportPointTensorIso L).hom rfl =
      transportSquareBasePre (transportPointProjection E ▷ K) (snd E K)
        (transportPointTensorIso K).hom rfl ≫
          transportSquareTensorPre (transportPointProjection E) i := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ transportSquarePointed (transportPointProjection E ▷ L) =
      (transportSquareBasePre (transportPointProjection E ▷ K) (snd E K)
        (transportPointTensorIso K).hom rfl ≫ transportSquareTensorPre
          (transportPointProjection E) i) ≫ transportSquarePointed (transportPointProjection E ▷ L)
    rw [Category.assoc, transportSquareBasePre_pointed, pointProductSquarePre_pointed,
      Category.assoc, transportSquareTensorPre_pointed, ← Category.assoc,
      transportSquareBasePre_pointed]
  · change (_ ≫ _) ≫ transportSquareDiagram (transportPointProjection E ▷ L) =
      (transportSquareBasePre (transportPointProjection E ▷ K) (snd E K)
        (transportPointTensorIso K).hom rfl ≫ transportSquareTensorPre
          (transportPointProjection E) i) ≫ transportSquareDiagram (transportPointProjection E ▷ L)
    rw [Category.assoc, transportSquareBasePre_diagram, ← Category.assoc,
      pointProductSquarePre_diagram]
    simp only [Category.assoc]
    rw [transportSquareTensorPre_diagram,
      ← Category.assoc (transportSquareBasePre (transportPointProjection E ▷ K) (snd E K)
        (transportPointTensorIso K).hom rfl), transportSquareBasePre_diagram]
    simp only [Category.assoc]
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
      transportPointTensorIso_naturality]

/-- 概要：点上の四角形の族の同型は実際のパラメーター制限に自然。
方針：底の正規化と内部 currying の二つの自然性を続ける。
規約：任意のパラメーターの射で全高次単体を保持する。
使われ方：区間の実際の境界制限を点上の族の境界制限へ移す。 -/
lemma pointProductSquareTensorIso_hom_naturality (E : SSet.{u + 1})
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductSquarePre E i ≫ (pointProductSquareTensorIso E L).hom =
      (pointProductSquareTensorIso E K).hom ≫
        (pre i).app (transportSquareSpace (transportPointProjection E)) := by
  dsimp only [pointProductSquareTensorIso, Iso.trans_hom, transportSquareBaseIso]
  rw [← Category.assoc, pointProductSquareBasePre_naturality, Category.assoc,
    transportSquareTensorIso_hom_naturality, ← Category.assoc]

end SerrePositivity.InfinityCategories

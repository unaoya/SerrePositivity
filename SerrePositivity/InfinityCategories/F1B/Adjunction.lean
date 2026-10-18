module

public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
概要：quasicategory の単位・余単位による随伴。
方針：Mathlib の `SSet.QCat.strictBicategory` の双圏随伴を使う。
規約：二胞体は h Fun の射であり、hX と hY の随伴で代用しない。
使われ方：Kerodon Def 6.1.1.1、Def 6.2.1.1、Remark 6.2.1.4、HTT §5.2。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合として与えた quasicategory を双圏の対象とする。
方針：充満部分圏の対象を作る。規約：宇宙は変えない。
使われ方：Kerodon Remark 6.2.1.4 のホモトピー双圏。 -/
abbrev qcatOf (X : SSet.{u}) [Quasicategory X] : SSet.QCat.{u} := ⟨X, inferInstance⟩

/-- 概要：単体集合の射を双圏の一胞体にする。
方針：充満部分圏の射を使う。規約：底の射を変えない。
使われ方：Kerodon Remark 6.2.1.4。 -/
abbrev qcatMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) :
    qcatOf X ⟶ qcatOf Y := ObjectProperty.homMk F

/-- 概要：quasicategory の関手の随伴。
方針：単位・余単位と h Fun 内の三角恒等式を持つ双圏随伴を使う。
規約：単位・余単位を可逆とは仮定しない。
使われ方：Kerodon Def 6.2.1.1・Remark 6.2.1.4、HTT §5.2。 -/
abbrev QCatAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) (G : Y ⟶ X) := Bicategory.Adjunction (qcatMap F) (qcatMap G)

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：双圏の Hom 圏から関手単体集合のホモトピー圏への表示。
方針：Cat への豊穣構造の底の二胞体を取る。規約：対象は既存の functorVertex。
使われ方：Kerodon Remark 6.2.1.4、A3a の FunctorIso との接続。 -/
def qcatHomFunctor (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    (qcatOf X ⟶ qcatOf Y) ⥤ hoFunctor.obj ((ihom X).obj Y) where
  obj F := SSet.HomotopyCategory.mk (functorVertex F.hom)
  map α := CatEnrichedOrdinary.Hom.base α

/-- 概要：h Fun の射と双圏の二胞体は同じデータ。
方針：豊穣 Hom の包みを外す。規約：ホモトピー圏間の自然変換への忘却ではない。
使われ方：Kerodon Remark 6.2.1.4 の二胞体の同定。 -/
def qcatCellEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F G : X ⟶ Y) :
    (qcatMap F ⟶ qcatMap G) ≃
      ((SSet.HomotopyCategory.mk (functorVertex F) : hoFunctor.obj ((ihom X).obj Y)) ⟶
        SSet.HomotopyCategory.mk (functorVertex G)) where
  toFun α := CatEnrichedOrdinary.Hom.base α
  invFun α := CatEnrichedOrdinary.Hom.mk α
  left_inv _ := rfl
  right_inv _ := rfl

/-- 概要：単体的ホモトピーを関手単体集合の辺として表す。
方針：curry した区間の射の一次単体を取り、両端を計算する。
規約：区間の向きは A1c と同じ 0 から 1。
使われ方：Kerodon Remark 6.2.1.4、単位・余単位の代表。 -/
noncomputable def functorEdgeOfHomotopy {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex (SSet.ι₀ ≫ H)) (functorVertex (SSet.ι₁ ≫ H)) where
  edge := SSet.yonedaEquiv (curry H)
  src_eq := by
    change ((ihom X).obj Y).map (SimplexCategory.δ (1 : Fin 2)).op
      (SSet.yonedaEquiv (curry H)) = _
    simpa only [Equiv.symm_apply_apply, uncurry_curry, SimplicialObject.δ] using
      (functorVertex_uncurry_zero (SSet.yonedaEquiv (curry H))).symm
  tgt_eq := by
    change ((ihom X).obj Y).map (SimplexCategory.δ (0 : Fin 2)).op
      (SSet.yonedaEquiv (curry H)) = _
    simpa only [Equiv.symm_apply_apply, uncurry_curry, SimplicialObject.δ] using
      (functorVertex_uncurry_one (SSet.yonedaEquiv (curry H))).symm

/-- 概要：単体的ホモトピーの類を双圏の二胞体にする。
方針：curry した辺の homMk を h Fun の表示同値で戻す。
規約：可逆性を仮定しない。始域・標的は quasicategory。
使われ方：Kerodon Def 6.2.1.1、A1c のホモトピーの二胞体表示。 -/
noncomputable def qcatCellOfHomotopy {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (H : X ⊗ Δ[1] ⟶ Y) : qcatMap (SSet.ι₀ ≫ H) ⟶ qcatMap (SSet.ι₁ ≫ H) :=
  (qcatCellEquiv _ _).symm (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfHomotopy H))

/-- 概要：双圏の可逆二胞体を既存の FunctorIso にする。
方針：Hom 圏の表示関手で同型を写す。規約：底の関手は変えない。
使われ方：Kerodon §6.1.3、A3a の同型 API。 -/
def qcatIsoToFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G : X ⟶ Y} (e : qcatMap F ≅ qcatMap G) : FunctorIso F G :=
  (qcatHomFunctor X Y).mapIso e

namespace QCatAdjunction

/-- 概要：恒等関手の自己随伴。
方針：双圏の恒等随伴。規約：指定された同じ対象を使う。
使われ方：Kerodon §6.1.1。 -/
def refl (X : SSet.{u}) [Quasicategory X] : QCatAdjunction (𝟙 X) (𝟙 X) :=
  Bicategory.Adjunction.id (qcatOf X)

/-- 概要：随伴の合成。
方針：双圏の合成定理を使う。規約：右随伴の順序は逆。
使われ方：Kerodon Cor 6.1.5.5、Remark 6.2.1.8。 -/
def comp {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} {F' : Y ⟶ Z} {G' : Z ⟶ Y}
    (a : QCatAdjunction F G) (b : QCatAdjunction F' G') :
    QCatAdjunction (F ≫ F') (G' ≫ G) := Bicategory.Adjunction.comp a b

/-- 概要：同じ左随伴の右随伴は h Fun で同型。
方針：恒等二胞体の mate を取る。規約：関手そのものの等式は主張しない。
使われ方：Kerodon §6.1.3、Remark 6.2.1.4。 -/
def rightAdjointIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G G' : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F G') :
    qcatMap G ≅ qcatMap G' := Bicategory.conjugateIsoEquiv a b (Iso.refl _)

/-- 概要：同じ右随伴の左随伴は h Fun で同型。
方針：右側の恒等同型の逆 mate を取る。規約：一意性は二胞体の同型。
使われ方：Kerodon §6.1.3、Remark 6.2.1.4。 -/
def leftAdjointIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F' G) :
    qcatMap F ≅ qcatMap F' := ((Bicategory.conjugateIsoEquiv a b).symm (Iso.refl _)).symm

/-- 概要：随伴の単位を h Fun(X,X) で取り出す。
方針：二胞体の表示同値を使う。規約：対象ごとの単位だけに忘却しない。
使われ方：Kerodon Def 6.2.1.1。 -/
def unitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (SSet.HomotopyCategory.mk (functorVertex (𝟙 X)) : hoFunctor.obj ((ihom X).obj X)) ⟶
      SSet.HomotopyCategory.mk (functorVertex (F ≫ G)) :=
  qcatCellEquiv _ _ a.unit

/-- 概要：随伴の余単位を h Fun(Y,Y) で取り出す。
方針：二胞体の表示同値を使う。規約：余単位を可逆としない。
使われ方：Kerodon Def 6.2.1.1。 -/
def counitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (SSet.HomotopyCategory.mk (functorVertex (G ≫ F)) : hoFunctor.obj ((ihom Y).obj Y)) ⟶
      SSet.HomotopyCategory.mk (functorVertex (𝟙 Y)) :=
  qcatCellEquiv _ _ a.counit

/-- 概要：同じ左随伴の右随伴間の FunctorIso。
方針：mate で得た同型を A3a の型に移す。規約：h Fun 内の同型。
使われ方：Kerodon Remark 6.2.1.19。 -/
def rightAdjointFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G G' : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F G') :
    FunctorIso G G' := qcatIsoToFunctorIso (rightAdjointIso a b)

/-- 概要：同じ右随伴の左随伴間の FunctorIso。
方針：mate の逆同型を A3a の型に移す。規約：h Fun 内の同型。
使われ方：Kerodon §6.1.3。 -/
def leftAdjointFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F' G) :
    FunctorIso F F' := qcatIsoToFunctorIso (leftAdjointIso a b)

/-- 概要：左三角恒等式を h Fun(X,Y) の等式として表示する。
方針：双圏の三角恒等式を Hom 圏の表示関手で写す。
規約：端点の単位子を明記し、単体集合の射の厳密な等式に強めない。
使われ方：Kerodon Def 6.2.1.1 の (Z1)。 -/
lemma left_triangle_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (qcatHomFunctor X Y).map (Bicategory.leftZigzag a.unit a.counit) =
      (qcatHomFunctor X Y).map
        ((Bicategory.leftUnitor (qcatMap F)).hom ≫ (Bicategory.rightUnitor (qcatMap F)).inv) :=
  congrArg (qcatHomFunctor X Y).map a.left_triangle

/-- 概要：右三角恒等式を h Fun(Y,X) の等式として表示する。
方針：双圏の三角恒等式を Hom 圏の表示関手で写す。
規約：端点の単位子を明記する。
使われ方：Kerodon Def 6.2.1.1 の (Z2)。 -/
lemma right_triangle_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (qcatHomFunctor Y X).map (Bicategory.rightZigzag a.unit a.counit) =
      (qcatHomFunctor Y X).map
        ((Bicategory.rightUnitor (qcatMap G)).hom ≫ (Bicategory.leftUnitor (qcatMap G)).inv) :=
  congrArg (qcatHomFunctor Y X).map a.right_triangle

/-- 概要：任意のパラメータ quasicategory 上の二胞体の adjunct 対応。
方針：双圏の Hom 随伴と h Fun の表示同値を合成する。
規約：これは h Fun の Hom の全単射。写像空間そのものの同値は別途証明する。
使われ方：Kerodon Prop 6.2.1.17 のパラメータを入れた証明の準備。 -/
def homEquiv {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (U : Z ⟶ X) (V : Z ⟶ Y) :
    ((SSet.HomotopyCategory.mk (functorVertex (U ≫ F)) : hoFunctor.obj ((ihom Z).obj Y)) ⟶
      SSet.HomotopyCategory.mk (functorVertex V)) ≃
    ((SSet.HomotopyCategory.mk (functorVertex U) : hoFunctor.obj ((ihom Z).obj X)) ⟶
      SSet.HomotopyCategory.mk (functorVertex (V ≫ G))) :=
  (qcatCellEquiv (U ≫ F) V).symm |>.trans
    ((Bicategory.Adjunction.homEquiv₂ a (g := qcatMap U) (h := qcatMap V)).trans
      (qcatCellEquiv U (V ≫ G)))

end QCatAdjunction
end SerrePositivity.InfinityCategories

module
public import SerrePositivity.KST.SConstruction.SPathBoundary
public import SerrePositivity.KST.SConstruction.ReductionEquivalence

/-! # 定数経路を潰す点つき経路実現
概要：元の零段からの定数経路の切断の像を一点へ潰して基点を作る。
方針：切断の単射性と cofiber の普遍性を使う。
規約：経路図式自身の零段全体を潰す操作とは異なる。使われ方：弱可縮な点つき経路模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：経路実現の定数経路の切断は単射。
方針：零段への射影との合成が恒等であることを使う。
規約：図式の充填性は不要。使われ方：定数経路を潰す商写像の比較。 -/
instance simplicialPathDiagonalSection_mono (X : SimplicialObject SSet.{u}) :
    Mono (simplicialPathDiagonalSection X) :=
  mono_of_mono_fac (simplicialPathDiagonalSection_projection X)

/-- 概要：定数経路の切断は単体的図式の写像について自然。
方針：零段への唯一の単体作用素に対する自然性を各次数で評価する。
規約：厳密等号。使われ方：定数経路を潰す写像の降下。 -/
lemma simplicialPathDiagonalSection_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    f.app (Opposite.op ⦋0⦌) ≫ simplicialPathDiagonalSection Y =
      simplicialPathDiagonalSection X ≫
        simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f) := by
  apply NatTrans.ext
  funext d
  exact congrArg (fun k => k.app d) (f.naturality
    (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op).symm

/-- 概要：元の零段の定数経路の像を基点へ潰した経路の対角。
方針：定数切断の cofiber を取る。
規約：選んだ零対象は使わない。使われ方：点つきの経路全空間。 -/
def reducedPathDiagonal (X : SimplicialObject SSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (simplicialPathDiagonalSection X)

/-- 概要：元の経路実現から定数経路を潰す商への射影。
方針：cofiber の標準射影。
規約：底の単体集合の射。使われ方：元の経路との比較。 -/
def pathDiagonalReductionQuotient (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ (reducedPathDiagonal X).right :=
  PointedObject.cofiberQuotient (simplicialPathDiagonalSection X)

/-- 概要：定数経路を潰した点つき経路実現の図式の射への作用。
方針：切断の自然性から像が基点へ写ることを示し、cofiber の普遍性で降ろす。
規約：単体的写像は任意。使われ方：点つき経路模型の関手性。 -/
def reducedPathDiagonalMap {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    reducedPathDiagonal X ⟶ reducedPathDiagonal Y :=
  PointedObject.cofiberDesc (simplicialPathDiagonalSection X) (reducedPathDiagonal Y)
    (simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f) ≫
      pathDiagonalReductionQuotient Y) (by
      rw [← Category.assoc, ← simplicialPathDiagonalSection_naturality, Category.assoc]
      change f.app (Opposite.op ⦋0⦌) ≫
        (simplicialPathDiagonalSection Y ≫
          PointedObject.cofiberQuotient (simplicialPathDiagonalSection Y)) = _
      rw [PointedObject.cofiberQuotient_condition, ← Category.assoc, comp_toUnit]
      rfl)

/-- 概要：降ろした写像は商射影との合成で元の経路の写像を回収する。
方針：cofiber の降下の合成式。
規約：厳密等号。使われ方：関手法則と境界の比較。 -/
lemma reducedPathDiagonalMap_quotient {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalMap f).right =
      simplicialDiagonalFunctor.map (Functor.whiskerLeft SimplexPrefix.functor.op f) ≫
        pathDiagonalReductionQuotient Y := PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：元の零段が弱可縮なら定数経路を潰す商射影は全 anodyne 反転関手で可逆。
方針：切断の単射性と、弱可縮な部分を潰す商写像の比較を使う。
規約：零段や経路の Kan 性は不要。使われ方：点つき経路の弱可縮性。 -/
lemma pathDiagonalReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u})
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (X.obj (Opposite.op ⦋0⦌))))) :
    IsIso (L.map (pathDiagonalReductionQuotient X)) :=
  cofiberQuotient_image_isIso_of_localized_toPoint L hL (simplicialPathDiagonalSection X) hX

/-- 概要：定数経路を潰す点つき経路実現は単体的図式について関手。
方針：商写像の回収式で恒等・合成を元の対角の関手法則へ戻す。
規約：追加の選択なし。使われ方：点つき経路の自然な Kan 模型。 -/
def reducedPathDiagonalFunctor :
    (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u} where
  obj := reducedPathDiagonal
  map := reducedPathDiagonalMap
  map_id X := by
    apply PointedObject.cofiber_hom_ext (simplicialPathDiagonalSection X)
    change pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalMap (𝟙 X)).right =
      pathDiagonalReductionQuotient X
    rw [reducedPathDiagonalMap_quotient]
    have hi : Functor.whiskerLeft SimplexPrefix.functor.op (𝟙 X) = 𝟙 (simplicialPath X) := rfl
    rw [hi]
    exact (congrArg (fun k => k ≫ pathDiagonalReductionQuotient X)
      (simplicialDiagonalFunctor.map_id (simplicialPath X))).trans (Category.id_comp _)
  map_comp {X Y Z} f g := by
    apply PointedObject.cofiber_hom_ext (simplicialPathDiagonalSection X)
    change pathDiagonalReductionQuotient X ≫ (reducedPathDiagonalMap (f ≫ g)).right =
      pathDiagonalReductionQuotient X ≫
        ((reducedPathDiagonalMap f).right ≫ (reducedPathDiagonalMap g).right)
    have hc : Functor.whiskerLeft SimplexPrefix.functor.op (f ≫ g) =
        Functor.whiskerLeft SimplexPrefix.functor.op f ≫
          Functor.whiskerLeft SimplexPrefix.functor.op g := rfl
    rw [reducedPathDiagonalMap_quotient, hc,
      simplicialDiagonalFunctor.map_comp, Category.assoc, ← reducedPathDiagonalMap_quotient,
      ← Category.assoc, ← reducedPathDiagonalMap_quotient, Category.assoc]

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.OneDirectionBoundaryNaturality

/-! # 一次方向を固定した実現の境界商と比較
概要：残りの全零境界を潰し、一次方向を消す比較を境界商へ降ろす。
方針：境界の像の包含と cofiber の普遍性を使う。
規約：商の比較の弱同値性は別に証明する。使われ方：反復間の構造射の源の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：入力の射を一次方向の全零境界へ制限する。
方針：像の包含を部分複体へ持ち上げる。
規約：全高次単体を保つ。使われ方：境界商の関手性。 -/
def oneDirectionBoundaryMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionFatBoundary r X : SSet.{u}) ⟶ (oneDirectionFatBoundary r Y : SSet.{u}) :=
  Subcomplex.lift ((oneDirectionFatBoundary r X).ι ≫ (oneDirectionRealizationFunctor r).map f) (by
    simpa only [Subcomplex.image_eq_range] using oneDirectionFatBoundary_image_le r f)

/-- 概要：境界に制限した写像は元の写像を回収する。
方針：部分複体への持ち上げの式。
規約：厳密な等号。使われ方：商への降下条件。 -/
lemma oneDirectionBoundaryMap_ι (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionBoundaryMap r f ≫ (oneDirectionFatBoundary r Y).ι =
      (oneDirectionFatBoundary r X).ι ≫ (oneDirectionRealizationFunctor r).map f := Subcomplex.lift_ι _ _

/-- 概要：正の反復の一次を固定した残りの全零境界を一点へ潰した実現。
方針：境界の包含の通常の cofiber を取る。
規約：残りの各零方向全体を潰す。使われ方：反復間の構造射の標的。 -/
def oneDirectionReducedRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (oneDirectionFatBoundary (r + 1) X).ι

/-- 概要：反復 core S の実現から残りの全零境界を潰す商への射。
方針：cofiber の射影を使う。
規約：全境界が商の基点へ写る。使われ方：旧実現との比較。 -/
def oneDirectionReductionQuotient (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionRealizationFunctor (r + 1)).obj X ⟶ (oneDirectionReducedRealization r X).right :=
  PointedObject.cofiberQuotient (oneDirectionFatBoundary (r + 1) X).ι

/-- 概要：入力の射は境界全体を潰す商間の点つき写像を誘導する。
方針：境界への制限と cofiber の関係式を合成する。
規約：基点を厳密に保存する。使われ方：反復実現の自然性。 -/
def oneDirectionReducedRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReducedRealization r X ⟶ oneDirectionReducedRealization r Y :=
  PointedObject.cofiberDesc (oneDirectionFatBoundary (r + 1) X).ι (oneDirectionReducedRealization r Y)
    ((oneDirectionRealizationFunctor (r + 1)).map f ≫ oneDirectionReductionQuotient r Y) (by
      calc
        (oneDirectionFatBoundary (r + 1) X).ι ≫
            (oneDirectionRealizationFunctor (r + 1)).map f ≫ oneDirectionReductionQuotient r Y =
            (oneDirectionBoundaryMap (r + 1) f ≫ (oneDirectionFatBoundary (r + 1) Y).ι) ≫
              oneDirectionReductionQuotient r Y := by
          rw [← Category.assoc, oneDirectionBoundaryMap_ι]
        _ = oneDirectionBoundaryMap (r + 1) f ≫
            toUnit (oneDirectionFatBoundary (r + 1) Y : SSet.{u}) ≫
              (oneDirectionReducedRealization r Y).hom := by
          rw [Category.assoc]
          exact congrArg (fun q => oneDirectionBoundaryMap (r + 1) f ≫ q)
            (PointedObject.cofiberQuotient_condition (oneDirectionFatBoundary (r + 1) Y).ι)
        _ = toUnit (oneDirectionFatBoundary (r + 1) X : SSet.{u}) ≫
            (oneDirectionReducedRealization r Y).hom := by rw [← Category.assoc, comp_toUnit])

/-- 概要：境界の商の写像は元の実現の写像を回収する。
方針：cofiber の普遍性の式。
規約：全単体での等号。使われ方：関手法則と比較の自然性。 -/
lemma oneDirectionReducedRealizationMap_quotient (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r f).right =
      (oneDirectionRealizationFunctor (r + 1)).map f ≫ oneDirectionReductionQuotient r Y :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：一次を固定した残りの全零境界を潰す点つき反復実現は入力の関手。
方針：商の射の外延性で恒等・合成を元の実現へ戻す。
規約：選択した零対象の保存を要求しない。使われ方：連結スペクトルの自然性。 -/
def oneDirectionReducedRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} where
  obj := oneDirectionReducedRealization r
  map := oneDirectionReducedRealizationMap r
  map_id X := by
    apply PointedObject.cofiber_hom_ext (oneDirectionFatBoundary (r + 1) X).ι
    change oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r (𝟙 X)).right =
      oneDirectionReductionQuotient r X
    rw [oneDirectionReducedRealizationMap_quotient, CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply PointedObject.cofiber_hom_ext (oneDirectionFatBoundary (r + 1) X).ι
    calc
      oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r (f ≫ g)).right =
          (oneDirectionRealizationFunctor (r + 1)).map (f ≫ g) ≫ oneDirectionReductionQuotient r Z :=
        oneDirectionReducedRealizationMap_quotient r _
      _ = (oneDirectionRealizationFunctor (r + 1)).map f ≫ (oneDirectionRealizationFunctor (r + 1)).map g ≫
          oneDirectionReductionQuotient r Z := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r f).right ≫
          (oneDirectionReducedRealizationMap r g).right := by
        rw [← oneDirectionReducedRealizationMap_quotient, ← Category.assoc,
          ← oneDirectionReducedRealizationMap_quotient, Category.assoc]
      _ = oneDirectionReductionQuotient r X ≫
          (oneDirectionReducedRealizationMap r f ≫ oneDirectionReducedRealizationMap r g).right := rfl

/-- 概要：残りの全零境界を潰す商写像は入力について自然。
方針：商の回収式を使う。
規約：厳密な自然変換。使われ方：元の実現との自然な比較。 -/
def oneDirectionReductionNat (r : ℕ) : oneDirectionRealizationFunctor (r + 1) ⟶
    oneDirectionReducedRealizationFunctor r ⋙ PointedSimplicialSet.forget where
  app := oneDirectionReductionQuotient r
  naturality {_X _Y} f := (oneDirectionReducedRealizationMap_quotient r f).symm


end SerrePositivity.KST.SConstruction

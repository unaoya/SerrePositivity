module
public import SerrePositivity.KST.SConstruction.ZeroBoundary
public import SerrePositivity.KST.SConstruction.ZeroDirectionsNaturality

/-! # 全零方向の境界を潰す自然な反復実現
概要：個々の零方向の像の合併全体を一点へ潰して、反復実現の点つき関手を作る。
方針：境界の像の自然性と cofiber の普遍性を使い、弱可縮性で商写像を比較する。
規約：反復間の構造写像や delooping は別工程。使われ方：Σ の境界を厳密に潰す模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：入力の射は零方向の境界の任意の有限合併を保存する。
方針：各像の保存を有限上限と preimage の単調性へ移す。
規約：chosen zero の保存を要求しない。使われ方：境界への写像の制限。 -/
lemma zeroDirectionsBoundary_image_le {r : ℕ} (s t : Finset (Fin r)) {X Y : StableModel.{u}}
    (f : X ⟶ Y) :
    (zeroDirectionsBoundary s t X).image ((multiRealizationFunctor r).map f) ≤
      zeroDirectionsBoundary s t Y := by
  rw [Subcomplex.image_le_iff]
  apply Finset.sup_le
  intro i hi
  have hY : zeroDirectionsRange (insert i t) Y ≤ zeroDirectionsBoundary s t Y := by
    change zeroDirectionsRange (insert i t) Y ≤ s.sup (fun j => zeroDirectionsRange (insert j t) Y)
    exact Finset.le_sup (f := fun j => zeroDirectionsRange (insert j t) Y) hi
  exact (Subcomplex.image_le_iff _ _ _).1 ((zeroDirectionsRange_image_le (insert i t) f).trans hY)

/-- 概要：入力の射を全零方向の境界へ制限する。
方針：像の保存条件で部分複体へ持ち上げる。
規約：全ての高次単体を保持する。使われ方：境界の商の自然性。 -/
def zeroDirectionsFatBoundaryMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (zeroDirectionsFatBoundary r X : SSet.{u}) ⟶ (zeroDirectionsFatBoundary r Y : SSet.{u}) :=
  Subcomplex.lift ((zeroDirectionsFatBoundary r X).ι ≫ (multiRealizationFunctor r).map f) (by
    simpa only [zeroDirectionsFatBoundary, Subcomplex.image_eq_range] using zeroDirectionsBoundary_image_le Finset.univ ∅ f)

/-- 概要：境界に制限した写像は元の写像を回収する。
方針：部分複体への持ち上げの式。
規約：厳密な等号。使われ方：商への降下条件。 -/
lemma zeroDirectionsFatBoundaryMap_ι (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    zeroDirectionsFatBoundaryMap r f ≫ (zeroDirectionsFatBoundary r Y).ι =
      (zeroDirectionsFatBoundary r X).ι ≫ (multiRealizationFunctor r).map f := Subcomplex.lift_ι _ _

/-- 概要：正の反復の全零方向の境界を一点へ潰した実現。
方針：境界の包含の通常の cofiber を取る。
規約：同時零段だけでなく各零方向全体を潰す。使われ方：反復間の構造射の標的。 -/
def boundaryReducedRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (zeroDirectionsFatBoundary (r + 1) X).ι

/-- 概要：反復 core S の実現から全零境界を潰す商への射。
方針：cofiber の射影を使う。
規約：全境界が商の基点へ写る。使われ方：旧実現との比較。 -/
def boundaryReductionQuotient (r : ℕ) (X : StableModel.{u}) :
    multiDiagonalCoreSConstruction (r + 1) X ⟶ (boundaryReducedRealization r X).right :=
  PointedObject.cofiberQuotient (zeroDirectionsFatBoundary (r + 1) X).ι

/-- 概要：入力の射は境界全体を潰す商間の点つき写像を誘導する。
方針：境界への制限と cofiber の関係式を合成する。
規約：基点を厳密に保存する。使われ方：反復実現の自然性。 -/
def boundaryReducedRealizationMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryReducedRealization r X ⟶ boundaryReducedRealization r Y :=
  PointedObject.cofiberDesc (zeroDirectionsFatBoundary (r + 1) X).ι (boundaryReducedRealization r Y)
    ((multiRealizationFunctor (r + 1)).map f ≫ boundaryReductionQuotient r Y) (by
      calc
        (zeroDirectionsFatBoundary (r + 1) X).ι ≫
            (multiRealizationFunctor (r + 1)).map f ≫ boundaryReductionQuotient r Y =
            (zeroDirectionsFatBoundaryMap (r + 1) f ≫ (zeroDirectionsFatBoundary (r + 1) Y).ι) ≫
              boundaryReductionQuotient r Y := by
          rw [← Category.assoc, zeroDirectionsFatBoundaryMap_ι]
        _ = zeroDirectionsFatBoundaryMap (r + 1) f ≫
            toUnit (zeroDirectionsFatBoundary (r + 1) Y : SSet.{u}) ≫
              (boundaryReducedRealization r Y).hom := by
          rw [Category.assoc]
          exact congrArg (fun q => zeroDirectionsFatBoundaryMap (r + 1) f ≫ q)
            (PointedObject.cofiberQuotient_condition (zeroDirectionsFatBoundary (r + 1) Y).ι)
        _ = toUnit (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) ≫
            (boundaryReducedRealization r Y).hom := by rw [← Category.assoc, comp_toUnit])

/-- 概要：境界の商の写像は元の実現の写像を回収する。
方針：cofiber の普遍性の式。
規約：全単体での等号。使われ方：関手法則と比較の自然性。 -/
lemma boundaryReducedRealizationMap_quotient (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r f).right =
      (multiRealizationFunctor (r + 1)).map f ≫ boundaryReductionQuotient r Y :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：全零方向の境界を潰す点つき反復実現は入力の関手。
方針：商の射の外延性で恒等・合成を元の実現へ戻す。
規約：選択した零対象の保存を要求しない。使われ方：連結スペクトルの自然性。 -/
def boundaryReducedRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} where
  obj := boundaryReducedRealization r
  map := boundaryReducedRealizationMap r
  map_id X := by
    apply PointedObject.cofiber_hom_ext (zeroDirectionsFatBoundary (r + 1) X).ι
    change boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r (𝟙 X)).right =
      boundaryReductionQuotient r X
    rw [boundaryReducedRealizationMap_quotient, CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply PointedObject.cofiber_hom_ext (zeroDirectionsFatBoundary (r + 1) X).ι
    calc
      boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r (f ≫ g)).right =
          (multiRealizationFunctor (r + 1)).map (f ≫ g) ≫ boundaryReductionQuotient r Z :=
        boundaryReducedRealizationMap_quotient r _
      _ = (multiRealizationFunctor (r + 1)).map f ≫ (multiRealizationFunctor (r + 1)).map g ≫
          boundaryReductionQuotient r Z := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = boundaryReductionQuotient r X ≫ (boundaryReducedRealizationMap r f).right ≫
          (boundaryReducedRealizationMap r g).right := by
        rw [← boundaryReducedRealizationMap_quotient, ← Category.assoc,
          ← boundaryReducedRealizationMap_quotient, Category.assoc]
      _ = boundaryReductionQuotient r X ≫
          (boundaryReducedRealizationMap r f ≫ boundaryReducedRealizationMap r g).right := rfl

/-- 概要：全零境界を潰す商写像は入力について自然。
方針：商の回収式を使う。
規約：厳密な自然変換。使われ方：元の実現との自然な比較。 -/
def boundaryReductionNat (r : ℕ) : multiRealizationFunctor (r + 1) ⟶
    boundaryReducedRealizationFunctor r ⋙ PointedSimplicialSet.forget where
  app := boundaryReductionQuotient r
  naturality {_X _Y} f := (boundaryReducedRealizationMap_quotient r f).symm

/-- 概要：全零境界を潰す商写像は anodyne を反転する全関手で可逆。
方針：境界合併の弱可縮性と単射の cofiber の pushout cube 比較を使う。
規約：境界や実現の Kan 性は不要。使われ方：元の反復実現との同値比較。 -/
lemma boundaryReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (boundaryReductionQuotient r X)) :=
  cofiberQuotient_image_isIso_of_localized_toPoint L hL (zeroDirectionsFatBoundary (r + 1) X).ι
    (zeroDirectionsFatBoundary_toPoint_localized_isIso r X)

/-- 概要：全零境界を潰した実現を点つき Kan 置換する関手。
方針：L9 の点つき Kan 置換関手と合成する。
規約：反復間の構造射は別に構成する。使われ方：スペクトルの各段の Kan 模型。 -/
def boundaryKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  boundaryReducedRealizationFunctor r ⋙ Spectra.PointedKanReplacement.functor

/-- 概要：全零境界を潰す実現の置換の各値は Kan。
方針：L9 の置換の Kan 性を使う。
規約：全ての正の反復に適用する。使われ方：Ω 条件の入力。 -/
instance boundaryKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((boundaryKanRealizationFunctor r).obj X).right) :=
  Spectra.PointedKanReplacement.obj_kanComplex _

end SerrePositivity.KST.SConstruction

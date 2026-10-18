module
public import SerrePositivity.KST.SConstruction.OneDirectionBoundary

/-! # 一次方向を固定した実現の零境界の自然性
概要：入力の射と一次方向を消す比較は、残りの零方向の像を保存する。
方針：零段の包含の自然性を各単体の原像へ適用する。
規約：零対象の選択を保存する仮定は不要。使われ方：点つき商の比較の降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：一次を固定した残りの零方向の実現は入力について関手的。
方針：多単体的 core を零方向で制限し対角を取る。
規約：外側の次数は常に 1。使われ方：零境界の包含の自然性。 -/
def oneDirectionZeroRealizationFunctor (r : ℕ) (j : Fin r) : StableModel.{u} ⥤ SSet.{u} where
  obj X := simplicialDiagonalFunctor.obj (oneDirectionZeroDiagram r j X)
  map f := simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
    (Functor.whiskerLeft (zeroDirectionsIndex {j}) (Functor.whiskerLeft (oneDirectionIndex r)
      ((multiCoreSConstructionFunctor (r + 1)).map f))))
  map_id X := by
    rw [CategoryTheory.Functor.map_id]
    change simplicialDiagonalFunctor.map (𝟙 _) = 𝟙 _
    exact simplicialDiagonalFunctor.map_id _
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Functor.whiskerLeft_comp, CategoryTheory.Functor.map_comp]

/-- 概要：任意の多単体図式の零方向の包含は図式の射について自然。
方針：添字の零段の射について自然性を評価し、対角で写す。
規約：反復 S を展開しない一般形。使われ方：一次を固定した零境界の自然性。 -/
lemma diagonalZeroInclusion_naturality {r : ℕ} (s : Finset (Fin r))
    {M N : (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}} (f : M ⟶ N) :
    simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
      (Functor.whiskerRight (zeroDirectionsIndexNat s) M)) ≫
        simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r) f) =
      simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
        (Functor.whiskerLeft (zeroDirectionsIndex s) f)) ≫
          simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
            (Functor.whiskerRight (zeroDirectionsIndexNat s) N)) := by
  rw [← simplicialDiagonalFunctor.map_comp, ← simplicialDiagonalFunctor.map_comp]
  congr 1
  apply NatTrans.ext
  funext d
  exact f.naturality ((zeroDirectionsIndexNat s).app ((multiIndexDiagonal r).obj d))

/-- 概要：一次を固定した残りの零段の包含は入力について自然。
方針：多単体図式の一般の自然性へ入力の射を代入する。
規約：厳密な自然変換。使われ方：range の像の包含。 -/
def oneDirectionZeroInclusionNat (r : ℕ) (j : Fin r) :
    oneDirectionZeroRealizationFunctor.{u} r j ⟶ oneDirectionRealizationFunctor r where
  app X := oneDirectionZeroInclusion r j X
  naturality {_X _Y} f := (diagonalZeroInclusion_naturality {j}
    (Functor.whiskerLeft (oneDirectionIndex r)
      ((multiCoreSConstructionFunctor (r + 1)).map f))).symm

/-- 概要：零段の包含の自然変換の成分は既存の包含。
方針：前合成と対角の定義。
規約：厳密等号。使われ方：各単体の像の計算。 -/
lemma oneDirectionZeroInclusionNat_app (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    (oneDirectionZeroInclusionNat r j).app X = oneDirectionZeroInclusion r j X := rfl

/-- 概要：入力の射は一次方向を固定した各零方向の像を保つ。
方針：零段の原像を対応する実現の射で写す。
規約：全 cofiber 保存射。使われ方：全零境界の保存。 -/
lemma oneDirectionZeroRange_image_le (r : ℕ) (j : Fin r) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionZeroRange r j X).image ((oneDirectionRealizationFunctor r).map f) ≤
      oneDirectionZeroRange r j Y := by
  change (Subfunctor.range ((oneDirectionZeroInclusionNat r j).app X)).image
      ((oneDirectionRealizationFunctor r).map f) ≤
    Subfunctor.range ((oneDirectionZeroInclusionNat r j).app Y)
  rw [← Subfunctor.range_comp, ← (oneDirectionZeroInclusionNat r j).naturality f]
  exact Subfunctor.range_comp_le _ _

/-- 概要：入力の射は一次方向を固定した残りの全零境界を保つ。
方針：各方向の像の保存を上限へ移す。
規約：r=0 の空境界も含む。使われ方：点つき商の関手性。 -/
lemma oneDirectionFatBoundary_image_le (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionFatBoundary r X).image ((oneDirectionRealizationFunctor r).map f) ≤
      oneDirectionFatBoundary r Y := by
  rw [Subcomplex.image_le_iff]
  intro d x hx
  change ((oneDirectionRealizationFunctor r).map f).app d x ∈ (oneDirectionFatBoundary r Y).obj d
  simp only [oneDirectionFatBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, (Subcomplex.image_le_iff _ _ _).1 (oneDirectionZeroRange_image_le r j f) d hj⟩

/-- 概要：一次方向の比較は残りの零方向の像を対応する零方向の像へ送る。
方針：多単体的比較の添字に関する自然性を零段の包含へ適用する。
規約：標的は一次方向を消した反復の実現。使われ方：比較の境界商への降下。 -/
lemma oneDirectionComparison_zeroRange_image_le (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    (oneDirectionZeroRange r j X).image (oneDirectionRealizationComparison r X) ≤
      zeroDirectionsRange {j} X := by
  rw [Subcomplex.image_le_iff]
  intro d x hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨((multiCoreSOneComparison r X).app
    ((zeroDirectionsIndex {j}).obj ((multiIndexDiagonal r).obj d))).app d z, ?_⟩
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app ((multiCoreSOneComparison r X).naturality
      ((zeroDirectionsIndexNat {j}).app ((multiIndexDiagonal r).obj d))) d) z

/-- 概要：一次方向の比較は残りの全零境界を標的の全零境界へ送る。
方針：各零方向の像の保存を上限へ移す。
規約：反復数の追加前提なし。使われ方：比較の点つき商への降下。 -/
lemma oneDirectionComparison_fatBoundary_image_le (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionFatBoundary r X).image (oneDirectionRealizationComparison r X) ≤
      zeroDirectionsFatBoundary r X := by
  rw [Subcomplex.image_le_iff]
  intro d x hx
  simp only [oneDirectionFatBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  have hle : zeroDirectionsRange {j} X ≤ zeroDirectionsFatBoundary r X :=
    Finset.le_sup (f := fun k => zeroDirectionsRange (insert k ∅) X) (Finset.mem_univ j)
  exact hle d ((Subcomplex.image_le_iff _ _ _).1
    (oneDirectionComparison_zeroRange_image_le r j X) d hj)

end SerrePositivity.KST.SConstruction

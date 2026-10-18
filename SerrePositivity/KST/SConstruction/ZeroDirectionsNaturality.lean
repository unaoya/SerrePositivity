module
public import SerrePositivity.KST.SConstruction.ZeroDirectionsRanges

/-! # 零方向の境界の入力に関する自然性
概要：零方向を固定した実現とその像は安定な入力の射について自然。
方針：前合成の自然変換を core S の関手で写し、像の包含を各単体で確認する。
規約：chosen zero の保存を要求しない。使われ方：境界全体の商の関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定した零方向の実現は入力について関手的。
方針：多単体的 core の関手を零方向の添字で前合成し、対角を取る。
規約：全方向の順序を保持する。使われ方：境界の像の自然性。 -/
def zeroDirectionsRealizationFunctor {r : ℕ} (s : Finset (Fin r)) : StableModel.{u} ⥤ SSet.{u} :=
  multiCoreSConstructionFunctor r ⋙
    (Functor.whiskeringLeft _ _ _).obj (multiIndexDiagonal r ⋙ zeroDirectionsIndex s) ⋙
      simplicialDiagonalFunctor

/-- 概要：零方向の実現の包含は入力について自然。
方針：添字包含による前合成の自然変換を評価し、対角を取る。
規約：厳密な自然変換。使われ方：境界の商の関手性。 -/
def zeroDirectionsInclusionNat {r : ℕ} (s : Finset (Fin r)) :
    zeroDirectionsRealizationFunctor.{u} s ⟶ multiRealizationFunctor r :=
  Functor.whiskerRight (Functor.whiskerLeft (multiCoreSConstructionFunctor r)
    ((Functor.whiskeringLeft _ _ _).map
      (Functor.whiskerLeft (multiIndexDiagonal r) (zeroDirectionsIndexNat s)))) simplicialDiagonalFunctor

/-- 概要：自然変換の成分は既存の零方向の包含。
方針：whiskering の定義を展開する。
規約：厳密な等号。使われ方：像の自然性の各単体での照合。 -/
lemma zeroDirectionsInclusionNat_app {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    (zeroDirectionsInclusionNat s).app X = zeroDirectionsInclusion s X := rfl

/-- 概要：安定な入力の射は指定した零方向の像を保存する。
方針：包含の自然性で像の元の原像を具体的に写す。
規約：部分複体の image による保存条件。使われ方：境界合併への制限。 -/
lemma zeroDirectionsRange_image_le {r : ℕ} (s : Finset (Fin r)) {X Y : StableModel.{u}}
    (f : X ⟶ Y) :
    (zeroDirectionsRange s X).image ((multiRealizationFunctor r).map f) ≤ zeroDirectionsRange s Y := by
  rw [Subcomplex.image_le_iff]
  intro d x hx
  obtain ⟨z, rfl⟩ := hx
  change ((multiRealizationFunctor r).map f).app d ((zeroDirectionsInclusion s X).app d z) ∈
    (zeroDirectionsRange s Y).obj d
  refine ⟨((zeroDirectionsRealizationFunctor s).map f).app d z, ?_⟩
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app ((zeroDirectionsInclusionNat s).naturality f) d) z

end SerrePositivity.KST.SConstruction

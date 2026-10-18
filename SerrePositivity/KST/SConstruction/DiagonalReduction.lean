module
public import SerrePositivity.KST.SConstruction.DiagonalConnected
public import SerrePositivity.Spectra.Pointed.Cofiber
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # 零段全体を一点へ潰す自然な対角実現
概要：単体的単体集合の零段を対角内で一点へ潰し、選択なしの点つき実現を作る。
方針：零段の包含の単射性と自然性を証明し、通常の cofiber の普遍性を使う。
規約：この定義だけでは商写像の弱同値性を主張しない。使われ方：自然な K 空間の基点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：単体的単体集合の対角を取る関手。
方針：uncurry と二変数の対角への制限を合成する。
規約：Kan 性を要求しない。使われ方：商写像の自然性。 -/
def simplicialDiagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategoryᵒᵖ)

/-- 概要：零段から対角への写像は単射。
方針：各次数の退化に一つの面を合成して恒等を得る。
規約：任意の単体的単体集合。使われ方：零段を潰す pushout の比較。 -/
instance diagonalZeroColumn_mono (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Mono (diagonalZeroColumn X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y h
  have hh := congrArg ((X.map (SimplexCategory.const ⦋0⦌ d.unop 0).op).app d) h
  change ((X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫
    X.map (SimplexCategory.const ⦋0⦌ d.unop 0).op).app d) x =
    ((X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫
    X.map (SimplexCategory.const ⦋0⦌ d.unop 0).op).app d) y at hh
  rw [← X.map_comp] at hh
  have he : (SimplexCategory.const d.unop ⦋0⦌ 0).op ≫
      (SimplexCategory.const ⦋0⦌ d.unop 0).op = 𝟙 (Opposite.op ⦋0⦌) := Subsingleton.elim _ _
  rw [he, X.map_id] at hh
  exact hh

/-- 概要：零段の包含は単体的単体集合について自然。
方針：各次数で外側退化に対する自然性を評価する。
規約：厳密な自然性。使われ方：零段の商の関手性。 -/
def diagonalZeroColumnNat :
    (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (Opposite.op ⦋0⦌) ⟶ simplicialDiagonalFunctor where
  app X := diagonalZeroColumn X
  naturality {X Y} f := by
    apply NatTrans.ext
    funext d
    exact (NatTrans.congr_app (f.naturality (SimplexCategory.const d.unop ⦋0⦌ 0).op) d).symm

/-- 概要：零段を一つの基点へ潰した対角実現。
方針：零段の包含の通常の cofiber を取る。
規約：零頂点の選択を含まない。使われ方：自然な点つき K 空間模型。 -/
def reducedDiagonal (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (diagonalZeroColumn X)

/-- 概要：対角実現から零段を潰した実現への商写像。
方針：通常の cofiber の射影を使う。
規約：商の基点は零段全体の像。使われ方：元の実現との比較。 -/
def diagonalReductionQuotient (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj X ⟶ (reducedDiagonal X).right :=
  PointedObject.cofiberQuotient (diagonalZeroColumn X)

/-- 概要：単体的写像は零段を潰した実現間の点つき写像を誘導する。
方針：零段の自然性と cofiber の普遍性を使う。
規約：基点を厳密に保つ。使われ方：K の自然な基点。 -/
def reducedDiagonalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    reducedDiagonal X ⟶ reducedDiagonal Y :=
  PointedObject.cofiberDesc (diagonalZeroColumn X) (reducedDiagonal Y)
    (simplicialDiagonalFunctor.map f ≫ diagonalReductionQuotient Y) (by
      calc
        diagonalZeroColumn X ≫ simplicialDiagonalFunctor.map f ≫ diagonalReductionQuotient Y =
            (f.app (Opposite.op ⦋0⦌) ≫ diagonalZeroColumn Y) ≫ diagonalReductionQuotient Y := by
          exact congrArg (fun q => q ≫ diagonalReductionQuotient Y)
            (diagonalZeroColumnNat.naturality f).symm
        _ = f.app (Opposite.op ⦋0⦌) ≫ toUnit (Y.obj (Opposite.op ⦋0⦌)) ≫ (reducedDiagonal Y).hom := by
          exact congrArg (fun q => f.app (Opposite.op ⦋0⦌) ≫ q)
            (PointedObject.cofiberQuotient_condition (diagonalZeroColumn Y))
        _ = toUnit (X.obj (Opposite.op ⦋0⦌)) ≫ (reducedDiagonal Y).hom := by
          rw [← Category.assoc, comp_toUnit])

/-- 概要：商に降ろした写像は元の対角写像を厳密に回収する。
方針：cofiber の降下の式を使う。
規約：全単体での等号。使われ方：関手法則の検証。 -/
lemma reducedDiagonalMap_quotient {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    diagonalReductionQuotient X ≫ (reducedDiagonalMap f).right =
      simplicialDiagonalFunctor.map f ≫ diagonalReductionQuotient Y :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：零段を潰す点つき実現は関手。
方針：商の普遍性で恒等・合成法則を元の対角の法則へ戻す。
規約：選択した零対象の保存は要求しない。使われ方：K の関手性。 -/
def reducedDiagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u} where
  obj := reducedDiagonal
  map := reducedDiagonalMap
  map_id X := by
    apply PointedObject.cofiber_hom_ext (diagonalZeroColumn X)
    change diagonalReductionQuotient X ≫ (reducedDiagonalMap (𝟙 X)).right = diagonalReductionQuotient X
    rw [reducedDiagonalMap_quotient, simplicialDiagonalFunctor.map_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply PointedObject.cofiber_hom_ext (diagonalZeroColumn X)
    calc
      diagonalReductionQuotient X ≫ (reducedDiagonalMap (f ≫ g)).right =
          simplicialDiagonalFunctor.map (f ≫ g) ≫ diagonalReductionQuotient Z := reducedDiagonalMap_quotient _
      _ = simplicialDiagonalFunctor.map f ≫ simplicialDiagonalFunctor.map g ≫ diagonalReductionQuotient Z := by
        rw [simplicialDiagonalFunctor.map_comp, Category.assoc]
      _ = diagonalReductionQuotient X ≫ (reducedDiagonalMap f).right ≫ (reducedDiagonalMap g).right := by
        rw [← reducedDiagonalMap_quotient, ← Category.assoc, ← reducedDiagonalMap_quotient, Category.assoc]
      _ = diagonalReductionQuotient X ≫ (reducedDiagonalMap f ≫ reducedDiagonalMap g).right := rfl

/-- 概要：零段を潰す商写像は対角実現からの自然変換。
方針：商の写像の回収式を使う。
規約：自然性は厳密。使われ方：元の実現との自然な比較。 -/
def diagonalReductionNat : simplicialDiagonalFunctor ⟶
    reducedDiagonalFunctor ⋙ PointedSimplicialSet.forget where
  app := diagonalReductionQuotient
  naturality {_X _Y} f := (reducedDiagonalMap_quotient f).symm

end SerrePositivity.KST.SConstruction

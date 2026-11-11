module
public import SerrePositivity.KST.SConstruction.GappedDegenerateSquares
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexPrescribedExtension

/-! # Ar[2] の中央の正方形
概要：Ar[2] から最初と最後の零対角を除いた四頂点は標準正方形をなす。
方針：端点を四頂点へ切り詰める順序写像で正方形の包含の単射性と像を調べる。
規約：中央正方形は (0,1),(0,2),(1,1),(1,2)。
使われ方：BGT Lemma 7.3 の次数2の cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Ar[2] の中央正方形の包含。
方針：標準の区間正方形を使う。
規約：対角の零角は (1,1)。使われ方：選んだ cofiber の配置。 -/
def arTwoMiddleSquare : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ arNerve 2 :=
  arSquare 0 1 1 2 (by decide) le_rfl (by decide)

/-- 概要：Ar[2] の端点を中央正方形の二座標へ切り詰める順序写像。
方針：右端から1を引き、左端は1で切り詰める。
規約：中央の四頂点では逆写像。使われ方：包含の単射性。 -/
def arTwoMiddleRetractionOrder : Ar.{u} 2 →o ULift.{u} (Fin 2 × Fin 2) where
  toFun a := ULift.up (⟨a.down.val.2.val - 1, by have h := a.down.val.2.isLt; omega⟩,
    ⟨min a.down.val.1.val 1, by omega⟩)
  monotone' _ _ h := ⟨Nat.sub_le_sub_right h.2 1, min_le_min_right 1 h.1⟩

/-- 概要：中央正方形の順序写像の後の切り詰めは恒等。
方針：二座標の四つの場合を計算する。
規約：順序関手の厳密等号。使われ方：標準単体の積での逆律。 -/
lemma arTwoMiddleRetraction_order_comp :
    (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor ⋙
      arTwoMiddleRetractionOrder.{u}.toFunctor = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  rcases x with ⟨x, y⟩
  apply ULift.ext
  apply Prod.ext <;> apply Fin.ext
  · fin_cases x <;> rfl
  · fin_cases y <;> rfl

/-- 概要：Ar[2] から中央正方形への単体集合の切り詰め。
方針：順序写像の nerve を標準単体の積に戻す。
規約：像の外側の両頂点も定義される。使われ方：中央正方形の像の判定。 -/
def arTwoMiddleRetraction : arNerve.{u} 2 ⟶ Δ[1] ⊗ Δ[1] :=
  nerveMap arTwoMiddleRetractionOrder.toFunctor ≫ (prodStdSimplex.isoNerve 1 1).inv

/-- 概要：中央正方形の包含の後の切り詰めは恒等。
方針：順序関手の逆律と標準単体の積の同型を使う。
規約：単体集合の厳密等号。使われ方：中央正方形の単射性。 -/
lemma arTwoMiddleSquare_retraction : arTwoMiddleSquare.{u} ≫ arTwoMiddleRetraction = 𝟙 _ := by
  change (prodStdSimplex.isoNerve 1 1).hom ≫
    nerveMap ((arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor ⋙
      arTwoMiddleRetractionOrder.toFunctor) ≫ (prodStdSimplex.isoNerve 1 1).inv = _
  rw [arTwoMiddleRetraction_order_comp]
  exact (prodStdSimplex.isoNerve 1 1).hom_inv_id

/-- 概要：中央正方形の包含は単射。
方針：切り詰めによる左逆を使う。
規約：全次数の単射性。使われ方：像を標準正方形と同定する。 -/
instance arTwoMiddleSquare_mono : Mono arTwoMiddleSquare.{u} where
  right_cancellation f g h := by
    have he := congrArg (fun q => q ≫ arTwoMiddleRetraction) h
    simpa only [Category.assoc, arTwoMiddleSquare_retraction, Category.comp_id] using he

/-- 概要：Ar[2] の中央正方形が張る部分複体。
方針：包含の像を取る。
規約：図式の選択より前の部分複体。使われ方：両端の零頂点を補う延長。 -/
def arTwoMiddle : (arNerve.{u} 2).Subcomplex := Subcomplex.range arTwoMiddleSquare

/-- 概要：中央正方形の像は標準正方形と同型。
方針：単射の像への射が同型であることを使う。
規約：全次数での厳密な同型。使われ方：cofiber 正方形の部分図式への移送。 -/
def arTwoMiddleIso : (Δ[1] ⊗ Δ[1] : SSet.{u}) ≅ (arTwoMiddle : SSet.{u}) :=
  asIso (Subcomplex.toRange arTwoMiddleSquare)

/-- 概要：中央正方形の像の同型は Ar[2] への包含と可換。
方針：像への標準射の定義を使う。
規約：厳密等号。使われ方：既存の cofiber を回収する式。 -/
lemma arTwoMiddleIso_ι : arTwoMiddleIso.{u}.hom ≫ arTwoMiddle.ι = arTwoMiddleSquare := rfl

end SerrePositivity.KST.SConstruction

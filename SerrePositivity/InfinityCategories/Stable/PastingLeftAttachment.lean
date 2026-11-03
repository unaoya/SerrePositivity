module
public import SerrePositivity.InfinityCategories.Stable.PastingLeftSquareIso
public import SerrePositivity.InfinityCategories.Stable.PastingLeftSpanIso
public import SerrePositivity.InfinityCategories.Stable.PastingOuterCocone
public import SerrePositivity.InfinityCategories.Core.ColimitAttachment

/-! # 左押し出しによる余極限頂点の付加

概要：左四角形が押し出しなら、五頂点図式の余錐の余極限性は四頂点図式への制限で判定できる。
方針：部分複体の pushout を標準 span とその余錐の形へ移し、余極限付加の一般補題を適用する。
規約：値域は quasicategory。使われ方：S4 の貼り合わせ本体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：共通 span の標準形の左四角形への包含は標準 span の包含に一致する。
方針：長方形への単射を合成し、左 span と左四角形の包含の式を使う。
規約：射の厳密な等式。使われ方：pushout の標準形への移し替え。 -/
lemma pastingLeftSpanIso_toSquare :
    pastingLeftSpanIso.{u}.hom ≫ pastingLeftSpanToSquare =
      spanSquareBoundary ≫ pastingLeftSquareIso.hom := by
  apply (cancel_mono pastingLeftSquare.ι).1
  rw [Category.assoc, Category.assoc, pastingLeftSquareIso_hom_ι]
  exact pastingLeftSpanIso_hom_ι

/-- 概要：標準 span の余錐を左四角形として五頂点図式へ含める。
方針：余錐の正方形表示と左四角形の標準形を合成する。
規約：余錐頂点は (1,1)。使われ方：左押し出しの余極限頂点の付加。 -/
def pastingLeftAttachmentCone : join (horn 2 0 : SSet.{u}) Δ[0] ⟶ (pastingCorner : SSet.{u}) :=
  spanCoconeSquareIso.hom ≫ pastingLeftSquareIso.hom ≫
    Subcomplex.homOfLE pastingLeftSquare_le_corner

/-- 概要：五頂点図式は標準 span に左四角形の余錐を付加する pushout。
方針：共通 span の pushout を二つの標準形の同型で移す。
規約：単体集合の通常の pushout。使われ方：余極限付加の一般補題。 -/
lemma pastingLeftAttachment_isPushout :
    IsPushout (joinInl (horn 2 0 : SSet.{u}) Δ[0])
      (pastingLeftSpanIso.hom ≫ pastingLeftSpan.ι) pastingLeftAttachmentCone
      pastingOuterBaseToCorner := by
  apply pastingLeftSpan_isPushout.of_iso' pastingLeftSpanIso
    (spanCoconeSquareIso ≪≫ pastingLeftSquareIso) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.trans_hom, spanSquareBoundary, Category.assoc] using
      pastingLeftSpanIso_toSquare
  · rfl
  · rfl
  · rfl

/-- 概要：付加した標準余錐を長方形へ含めると左四角形の余錐表示になる。
方針：左四角形の標準形の包含の式を使う。
規約：形状の射の厳密な等式。使われ方：指定した左押し出しの余錐との一致。 -/
lemma pastingLeftAttachmentCone_ι :
    pastingLeftAttachmentCone.{u} ≫ pastingCorner.ι =
      spanCoconeSquareIso.hom ≫ (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  change (spanCoconeSquareIso.hom ≫ pastingLeftSquareIso.hom ≫
    Subcomplex.homOfLE pastingLeftSquare_le_corner) ≫ pastingCorner.ι = _
  have hi : Subcomplex.homOfLE pastingLeftSquare_le_corner ≫ pastingCorner.ι =
      pastingLeftSquare.{u}.ι := rfl
  rw [Category.assoc, Category.assoc, hi, pastingLeftSquareIso_hom_ι]

/-- 概要：左四角形が押し出しなら、五頂点図式から四頂点図式への coslice 制限は trivial Kan fibration。
方針：左四角形の余極限余錐を標準形の pushout に沿って付加する一般補題を使う。
規約：充填性そのものには quasicategory 性を仮定しない。
使われ方：貼り合わせの余極限性の保存と反映。 -/
lemma pastingCornerRestrict_outerBase_trivialKanFibration {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : IsPushoutSquare (pastingSquare F 2)) :
    TrivialKanFibration (sliceUnderRestrict (pastingCorner.ι ≫ F) pastingOuterBaseToCorner) := by
  apply cosliceRestriction_trivialKanFibration_of_colimit_attachment
    (pushoutCocone (pastingSquare F 2)) hleft
    (pastingLeftSpanIso.hom ≫ pastingLeftSpan.ι) pastingLeftAttachmentCone
    pastingOuterBaseToCorner pastingLeftAttachment_isPushout
  rw [← Category.assoc, pastingLeftAttachmentCone_ι, Category.assoc]
  rfl

/-- 概要：左四角形が押し出しなら、五頂点図式の余錐は四頂点図式への制限で余極限性を判定できる。
方針：制限の trivial Kan fibration による始対象性の保存と反映を使う。
規約：値域は quasicategory、余錐頂点は固定。
使われ方：S4 の右四角形と外側四角形の押し出し性の比較。 -/
lemma pastingCocone_isColimitCone_iff_outerCocone {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : IsPushoutSquare (pastingSquare F 2)) :
    IsColimitCone (pastingCocone F) ↔ IsColimitCone (pastingOuterCocone F) := by
  have := pastingCornerRestrict_outerBase_trivialKanFibration F hleft
  exact (qCatEquivalenceOfTrivialKanFibration
    (sliceUnderRestrict (pastingCorner.ι ≫ F) pastingOuterBaseToCorner)).isInitialVertex_iff
      (pastingCocone F)

end SerrePositivity.InfinityCategories

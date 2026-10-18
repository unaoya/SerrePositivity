module

public import SerrePositivity.KST.Comparison.FatSkeletonPushout
public import SerrePositivity.KST.Comparison.FatSkeletonRowRelations
public import SerrePositivity.KST.Comparison.SubcomplexUnionCocone

/-!
# 有限骨格の付着の実際の span

概要：境界の付着の pushout を span の余錐と自然変換として構成する。
方針：既証の付着の四角形の可換性と普遍性を使う。
規約：Segal 1974 Proposition 1.6 の各骨格の付着。
使われ方：Lemma 1.7 の実際の通常の pushout への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：次の骨格の付着を記述する span。
方針：境界から旧骨格への射と、新しい行への包含を取る。
規約：右脚は単射な境界の積の包含。
使われ方：通常の pushout の貼り合わせ定理の図式。
-/
def fatAttachmentSpan (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    WalkingSpan ⥤ SSet.{u} :=
  span (fatBoundaryAttachment F n)
    (F.obj (op ⦋n + 1⦌) ◁ (SSet.boundary (n + 1)).ι)

/--
概要：付着の span の右脚は単射である。
方針：部分対象の包含の単射性を積の単射保存に渡す。
規約：左脚の単射性は要求しない。
使われ方：二重写像円筒と通常の pushout の比較。
-/
instance fatAttachmentSpan_snd_mono (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    Mono ((fatAttachmentSpan F n).map WalkingSpan.Hom.snd) :=
  tensorLeft_mono_of_mono _ _

/--
概要：次の骨格を頂点とする付着の余錐。
方針：旧骨格の包含と新しい行の射を組み合わせる。
規約：可換性は実際の付着の pushout の四角形の等式。
使われ方：余極限の比較の具体的な余錐。
-/
def fatAttachmentCocone (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    Cocone (fatAttachmentSpan F n) :=
  PushoutCocone.mk (fatSkeletonStep F n) (fatSkeletonRow F (n + 1))
    (fatSkeleton_isPushout F n).w

/--
概要：付着の余錐は実際の余極限である。
方針：標準形から証明した付着の pushout の普遍性を使う。
規約：ホモトピー余極限を入力として仮定しない。
使われ方：Lemma 1.7 の各頂点から次の骨格への四角形。
-/
def fatAttachmentCoconeIsColimit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    IsColimit (fatAttachmentCocone F n) := (fatSkeleton_isPushout F n).isColimit

/--
概要：二重単体集合の射が誘導する付着の span の自然変換。
方針：境界・旧骨格・新しい行で対応する射を取り、自然性を組み合わせる。
規約：番号 n は保つ。
使われ方：二つの付着の pushout の比較。
-/
def fatAttachmentSpanMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ) :
    fatAttachmentSpan F n ⟶ fatAttachmentSpan G n :=
  spanHomMk (α.app (op ⦋n + 1⦌) ▷ (SSet.boundary (n + 1) : SSet.{u}))
    (fatSkeletonMap α n) (α.app (op ⦋n + 1⦌) ▷ Δ[n + 1])
    (fatBoundaryAttachment_map α n)
    (whisker_exchange (α.app (op ⦋n + 1⦌)) (SSet.boundary (n + 1)).ι)

/--
概要：骨格の射は付着の余錐の射と両立する。
方針：span の三つの頂点ごとに行と境界の自然性を使う。
規約：次の骨格の実際の制限写像を比較する。
使われ方：pushout の比較に必要な余錐の可換性。
-/
theorem fatAttachmentCocone_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (α : F ⟶ G) (n : ℕ) (d : WalkingSpan) :
    (fatAttachmentCocone F n).ι.app d ≫ fatSkeletonMap α (n + 1) =
      (fatAttachmentSpanMap α n).app d ≫ (fatAttachmentCocone G n).ι.app d := by
  rcases d with (_ | _ | _)
  · change (fatBoundaryAttachment F n ≫ fatSkeletonStep F n) ≫
      fatSkeletonMap α (n + 1) =
      (α.app (op ⦋n + 1⦌) ▷ (SSet.boundary (n + 1) : SSet.{u})) ≫
        fatBoundaryAttachment G n ≫ fatSkeletonStep G n
    have hstep : fatSkeletonStep F n ≫ fatSkeletonMap α (n + 1) =
        fatSkeletonMap α n ≫ fatSkeletonStep G n := rfl
    rw [Category.assoc, hstep, ← Category.assoc, fatBoundaryAttachment_map, Category.assoc]
  · apply (cancel_mono (fatSkeleton G (n + 1)).ι).mp
    simp only [Category.assoc, fatSkeletonMap_ι]
    rfl
  · exact fatSkeletonRowOfLE_map α (le_refl (n + 1))

end SerrePositivity.KST.Comparison

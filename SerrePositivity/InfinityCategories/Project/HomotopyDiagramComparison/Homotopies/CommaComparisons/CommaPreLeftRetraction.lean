module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# 全図式の左変数の比較の comma の元の分解への収縮

概要：Low 命題 3.7 の全図式の比較の各 comma を分解側の comma へ射影する。
方針：元の左成分へ射影し、右脚を指定終点へ固定した切断と自然変換を作る。
規約：元の中間射と可換条件を保持し、モデル構造は要求しない。
使われ方：全図式の比較への Quillen A の適用。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction

open CategoryTheory

variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]
  (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C) (T : Comma Q R)

/-- 概要：元の全図式の比較の comma から分解の comma への射影（Low 命題 3.7）。
方針：元の比較の左成分を取り出す。
規約：全ての元の可換三角形を保持する。
使われ方：全図式の comma の収縮の射影。 -/
def projection : CostructuredArrow (Comma.preLeft P Q R) T ⥤ CostructuredArrow P T.left where
  obj s := CostructuredArrow.mk (S := P) s.hom.left
  map f := CostructuredArrow.homMk f.left.left
    (congrArg CommaMorphism.left (CostructuredArrow.w f))
  map_id _s := CostructuredArrow.hom_ext _ _ rfl
  map_comp _f _g := CostructuredArrow.hom_ext _ _ rfl

/-- 概要：分解の comma の元の射を全図式の比較へ戻す（Low 命題 3.7）。
方針：右脚を T.right に固定し、元の左射と T の中間射を合成する。
規約：対象や射の代表の選択を使わない。
使われ方：全図式の comma の収縮の切断。 -/
def canonicalSection : CostructuredArrow P T.left ⥤ CostructuredArrow (Comma.preLeft P Q R) T where
  obj s := CostructuredArrow.mk (S := Comma.preLeft P Q R)
    (Y := (show Comma (P ⋙ Q) R from ⟨s.left, T.right, Q.map s.hom ≫ T.hom⟩))
    { left := s.hom
      right := 𝟙 T.right
      w := by
        change Q.map s.hom ≫ T.hom = (Q.map s.hom ≫ T.hom) ≫ R.map (𝟙 T.right)
        rw [R.map_id, Category.comp_id] }
  map {s t} f := CostructuredArrow.homMk
    { left := f.left
      right := 𝟙 T.right
      w := by
        change Q.map (P.map f.left) ≫ (Q.map t.hom ≫ T.hom) =
          (Q.map s.hom ≫ T.hom) ≫ R.map (𝟙 T.right)
        rw [R.map_id, Category.comp_id, ← Category.assoc, ← Q.map_comp, CostructuredArrow.w f] }
    (by
      apply CommaMorphism.ext
      · exact CostructuredArrow.w f
      · exact Category.id_comp _)
  map_id s := by
    apply CostructuredArrow.hom_ext
    exact CommaMorphism.ext rfl rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact CommaMorphism.ext rfl (Category.id_comp _).symm

/-- 概要：元の切断の後の射影は同じ分解の comma の恒等（Low 命題 3.7）。
方針：元の左対象と構造射の eta 則を使う。
規約：全対象・全射での厳密な関手の等式。
使われ方：元の nerve の収縮の切断の法則。 -/
lemma canonicalSection_projection : canonicalSection P Q R T ⋙ projection P Q R T = 𝟭 _ := rfl

/-- 概要：元の右成分が全図式の comma の収縮を与える（Low 命題 3.7）。
方針：元の比較の右成分を固定右脚への射に使い、元の三角形の整合を合成する。
規約：元の全対象と全射への自然性を保持する。
使われ方：全図式の comma と分解の comma の nerve のホモトピー比較。 -/
def contraction : 𝟭 _ ⟶ projection P Q R T ⋙ canonicalSection P Q R T where
  app s := CostructuredArrow.homMk
    { left := 𝟙 s.left.left
      right := s.hom.right
      w := by
        change Q.map (P.map (𝟙 s.left.left)) ≫ (Q.map s.hom.left ≫ T.hom) =
          s.left.hom ≫ R.map s.hom.right
        rw [P.map_id, Q.map_id, Category.id_comp]
        exact s.hom.w }
    (by
      apply CommaMorphism.ext
      · change P.map (𝟙 s.left.left) ≫ s.hom.left = s.hom.left
        rw [P.map_id, Category.id_comp]
      · exact Category.comp_id _)
  naturality s t f := by
    apply CostructuredArrow.hom_ext
    apply CommaMorphism.ext
    · change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change f.left.right ≫ t.hom.right = s.hom.right ≫ 𝟙 _
      exact (congrArg CommaMorphism.right (CostructuredArrow.w f)).trans
        (Category.comp_id _).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction

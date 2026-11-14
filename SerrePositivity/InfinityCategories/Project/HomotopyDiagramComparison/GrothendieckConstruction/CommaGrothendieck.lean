module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CostructuredArrowDiagram
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Equivalence

/-!
# 両脚の comma 圏と右脚に沿う Grothendieck 構成の同値

概要：Low 命題 3.7 の二変数の中間 Hom を元の右脚に沿う全図式で表示する。
方針：右脚を底、左脚と中間射の costructured arrow を fiber とする。
規約：元の射と可換条件を保持し、モデル構造や置換は要求しない。
使われ方：分解の余終性と終域の不変性の三本矢の全体への適用。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v' u'' v''

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck

open CategoryTheory

variable {K : Type u} [Category.{v} K] {J : Type u'} [Category.{v'} J]
  {C : Type u''} [Category.{v''} C] (Q : K ⥤ C) (R : J ⥤ C)

/-- 概要：元の中間 Hom の右変数に沿う Cat 値図式（Low 命題 3.7）。
方針：元の右射影と costructured arrow の後合成を合成する。
規約：恒等と合成を厳密に保つ。
使われ方：全三本矢を表示する Grothendieck 構成。 -/
abbrev diagram : J ⥤ Cat.{v, max u v''} := R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram Q

/-- 概要：元の全図式から同じ両脚の comma 圏への関手（Low 命題 3.7）。
方針：底を右脚、fiber の左対象を左脚、構造射を元の中間射へ送る。
規約：全ての可換正方形を元の射として保持する。
使われ方：三本矢の二変数の全図式の同定。 -/
def toComma : Grothendieck (diagram Q R) ⥤ Comma Q R where
  obj S := ⟨S.fiber.left, S.base, S.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, CostructuredArrow.w f.fiber⟩
  map_id S := by
    apply CommaMorphism.ext
    · change CostructuredArrow.Hom.left (Grothendieck.id S).fiber = 𝟙 S.fiber.left
      dsimp only [Grothendieck.id]
      rw [CostructuredArrow.eqToHom_left]
      rfl
    · rfl
  map_comp f g := by
    apply CommaMorphism.ext
    · change CostructuredArrow.Hom.left (f ≫ g).fiber = f.fiber.left ≫ g.fiber.left
      rw [Grothendieck.comp_fiber, CostructuredArrow.comp_left,
        CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
      exact Category.id_comp _
    · rfl

/-- 概要：全図式の射は元の二つの縦射で決まる（Low 命題 3.7）。
方針：右の底成分と左の fiber 成分を回収する。
規約：元の可換条件は命題として保持する。
使われ方：三本矢の全図式表示の忠実性。 -/
instance toComma_faithful : (toComma Q R).Faithful where
  map_injective {S T} f g h := by
    apply Grothendieck.ext f g (congrArg CommaMorphism.right h)
    apply CostructuredArrow.hom_ext
    have hh : f.fiber.left = g.fiber.left := congrArg CommaMorphism.left h
    rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    exact (Category.id_comp _).trans hh

/-- 概要：comma の全可換正方形は元の全図式の射から来る（Low 命題 3.7）。
方針：右射を底成分、左射と元の正方形を fiber 成分に使う。
規約：同じ元の二つの射を使う。
使われ方：三本矢の全図式表示の充満性。 -/
instance toComma_full : (toComma Q R).Full where
  map_surjective {_S _T} f :=
    ⟨{ base := f.right, fiber := CostructuredArrow.homMk f.left f.w },
      CommaMorphism.ext rfl rfl⟩

/-- 概要：全 comma 対象は元の右脚と中間射の fiber から来る（Low 命題 3.7）。
方針：元の右対象と同じ構造射を持つ costructured arrow を使う。
規約：対象と中間射を変更しない。
使われ方：三本矢の全図式表示の本質的全射性。 -/
instance toComma_essSurj : (toComma Q R).EssSurj where
  mem_essImage S := ⟨⟨S.right, CostructuredArrow.mk S.hom⟩, ⟨Iso.refl S⟩⟩

/-- 概要：元の両脚の comma を同じ全図式へ戻す（Low 命題 3.7）。
方針：元の右脚を底、左脚と中間射を fiber に使う。
規約：対象ごとの代表を選ばず、元の対象をそのまま使う。
使われ方：元の frame の全単体図式の厳密な因子分解。 -/
def fromComma : Comma Q R ⥤ Grothendieck (diagram Q R) where
  obj S := ⟨S.right, CostructuredArrow.mk (S := Q) S.hom⟩
  map f := ⟨f.right, CostructuredArrow.homMk f.left f.w⟩
  map_id S := by
    apply (toComma Q R).map_injective
    rw [(toComma Q R).map_id]
    exact CommaMorphism.ext rfl rfl
  map_comp f g := by
    apply (toComma Q R).map_injective
    rw [(toComma Q R).map_comp]
    exact CommaMorphism.ext rfl rfl

/-- 概要：右変数に沿う全図式は元の両脚の comma 圏と同値（Low 命題 3.7）。
方針：元の表示関手の充満忠実性と本質的全射性を束ねる。
規約：順関手は元の右脚と中間射を回収する toComma。
使われ方：特殊な三本矢への右比較のホモトピー余極限の表示。 -/
def equivalence : Grothendieck (diagram Q R) ≌ Comma Q R :=
  CategoryTheory.Equivalence.mk (toComma Q R) (fromComma Q R)
    (NatIso.ofComponents (fun S =>
      Grothendieck.isoMk (Iso.refl S.base)
        (CostructuredArrow.isoMk (Iso.refl S.fiber.left) (by
          change Q.map (𝟙 S.fiber.left) ≫ S.fiber.hom = S.fiber.hom ≫ R.map (𝟙 S.base)
          rw [Q.map_id, R.map_id, Category.id_comp, Category.comp_id]))) (by
      intro S T f
      apply (toComma Q R).map_injective
      rw [(toComma Q R).map_comp, (toComma Q R).map_comp]
      change (toComma Q R).map f ≫ 𝟙 _ = 𝟙 _ ≫ (toComma Q R).map f
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun S =>
      Comma.isoMk (Iso.refl S.left) (Iso.refl S.right) (by
        change Q.map (𝟙 S.left) ≫ S.hom = S.hom ≫ R.map (𝟙 S.right)
        rw [Q.map_id, R.map_id, Category.id_comp, Category.comp_id])) (by
      intro S T f
      change f ≫ 𝟙 _ = 𝟙 _ ≫ f
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck

module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitPathReplacement
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftConstantFamily

/-!
概要：path 置換上の標準相対左 Kan 条件は元の始域への射影で検出できる。
方針：局所余錐の path 置換での判定を標準余錐の後合成の式と合成する。
規約：元の U に fibration 性を要求しない。
使われ方：一般 U の写像空間比較を同値持ち上げを持つ置換へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：path 置換上の標準相対左 Kan 条件は射影後の元の条件と同値。
方針：各標準余錐の相対余極限条件を射影し、元の標準余錐と同定する。
規約：δ の単射性や充填性は不要。
使われ方：一般 U の局所条件の置換への移送。 -/
lemma kanIsRelativeLeftKanExtendedFrom_pathReplacement_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C)
    (F : C ⟶ equivalencePathReplacement U) :
    IsRelativeLeftKanExtendedFrom (equivalencePathReplacementMap U) δ F ↔
      IsRelativeLeftKanExtendedFrom U δ (F ≫ equivalencePathReplacementProjection U) := by
  have h (c : C _⦋0⦌) := kanIsRelativeColimitCone_equivalencePathReplacement_iff U
    (leftKanCanonicalCocone δ F c)
  have hc (c : C _⦋0⦌) : IsRelativeColimitCone (equivalencePathReplacementMap U)
      (leftKanCanonicalCocone δ F c) ↔ IsRelativeColimitCone U
        (leftKanCanonicalCocone δ (F ≫ equivalencePathReplacementProjection U) c) := by
    exact (h c).trans (kanIsRelativeColimitCone_congr U
      (by simp only [leftKanDiagram, Category.assoc]) _ _
      (kanLeftCanonicalCocone_postcomp_val δ F (equivalencePathReplacementProjection U) c).symm)
  exact ⟨fun h c ↦ (hc c).1 (h c), fun h c ↦ (hc c).2 (h c)⟩

/-- 概要：定値 path の切断は標準相対左 Kan 条件を保ち反映する。
方針：射影との合成が恒等射であることを前の判定へ代入する。
規約：元の U の充填性は不要。
使われ方：元の関手の写像空間を path 置換上で比較する入力。 -/
lemma kanIsRelativeLeftKanExtendedFrom_pathSection_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) :
    IsRelativeLeftKanExtendedFrom (equivalencePathReplacementMap U) δ
      (F ≫ equivalencePathReplacementSection U) ↔ IsRelativeLeftKanExtendedFrom U δ F := by
  have h := kanIsRelativeLeftKanExtendedFrom_pathReplacement_iff U δ
    (F ≫ equivalencePathReplacementSection U)
  simpa only [Category.assoc, equivalencePathReplacementSection_projection,
    Category.comp_id] using h

end SerrePositivity.InfinityCategories.F1B

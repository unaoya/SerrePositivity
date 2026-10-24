module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLimitTrivialComparison
public import SerrePositivity.InfinityCategories.F1B.KanExtension.PathReplacementLifting
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightConstantFamily

/-!
概要：path 置換上の標準相対右 Kan 条件は元の始域への射影で検出できる。
方針：局所錐の path 置換での判定を標準錐の後合成の式と合成する。
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

/-- 概要：path 置換上の相対極限錐は元の始域への像で検出できる。
方針：二つの端点評価を交換し、射影の自明 Kan 性を slice で消去する。
規約：元の U に充填性は要求しない。
使われ方：標準右 Kan 条件を path 置換へ移す局所判定。 -/
lemma kanIsRelativeLimitCone_equivalencePathReplacement_iff
    {K D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E)
    {F : K ⟶ equivalencePathReplacement U} (c : JoinCone F) :
    IsRelativeLimitCone (equivalencePathReplacementMap U) c ↔
      IsRelativeLimitCone U
        ((sliceOverPostcomp F (equivalencePathReplacementProjection U)).app
          (Opposite.op ⦋0⦌) c) := by
  let a := Limits.pullback.fst (equivalencePathEndpoint E 0) U
  have he : a ≫ equivalencePathEndpoint E 0 =
      equivalencePathReplacementProjection U ≫ U := Limits.pullback.condition
  have hh := congrArg (fun V : equivalencePathReplacement U ⟶ E ↦
    IsRelativeLimitCone V c) he
  exact (kanIsRelativeLimitCone_comp_iff_of_trivialKanFibration a
    (equivalencePathEndpoint E 1) c).trans
    ((kanIsRelativeLimitCone_comp_iff_of_trivialKanFibration a
      (equivalencePathEndpoint E 0) c).symm.trans
      (Iff.of_eq hh |>.trans
        (kanIsRelativeLimitCone_precomp_iff_of_trivialKanFibration
          (equivalencePathReplacementProjection U) U c)))

/-- 概要：標準右錐の後合成は後合成後の関手の標準右錐に等しい。
方針：標準錐の展開の合成の結合則。
規約：raw な錐の値の厳密な等式。
使われ方：path 置換の射影後の標準右錐の同定。 -/
lemma kanRightCanonicalCone_postcomp_val {K C D E : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (U : D ⟶ E) (c : C _⦋0⦌) :
    (rightKanCanonicalCone δ (F ≫ U) c).val = (rightKanCanonicalCone δ F c).val ≫ U :=
  (Category.assoc _ _ _).symm

/-- 概要：path 置換上の標準相対右 Kan 条件は射影後の元の条件と同値。
方針：各標準錐の相対極限条件を射影し、元の標準錐と同定する。
規約：δ の単射性や充填性は不要。
使われ方：一般 U の局所条件の置換への移送。 -/
lemma kanIsRelativeRightKanExtendedFrom_pathReplacement_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C)
    (F : C ⟶ equivalencePathReplacement U) :
    IsRelativeRightKanExtendedFrom (equivalencePathReplacementMap U) δ F ↔
      IsRelativeRightKanExtendedFrom U δ (F ≫ equivalencePathReplacementProjection U) := by
  have h (c : C _⦋0⦌) := kanIsRelativeLimitCone_equivalencePathReplacement_iff U
    (rightKanCanonicalCone δ F c)
  have hc (c : C _⦋0⦌) : IsRelativeLimitCone (equivalencePathReplacementMap U)
      (rightKanCanonicalCone δ F c) ↔ IsRelativeLimitCone U
        (rightKanCanonicalCone δ (F ≫ equivalencePathReplacementProjection U) c) := by
    exact (h c).trans (kanIsRelativeLimitCone_congr U
      (by simp only [rightKanDiagram, Category.assoc]) _ _
      (kanRightCanonicalCone_postcomp_val δ F (equivalencePathReplacementProjection U) c).symm)
  exact ⟨fun h c ↦ (hc c).1 (h c), fun h c ↦ (hc c).2 (h c)⟩

/-- 概要：定値 path の切断は標準相対右 Kan 条件を保ち反映する。
方針：射影との合成が恒等射であることを前の判定へ代入する。
規約：元の U の充填性は不要。
使われ方：元の関手の写像空間を path 置換上で比較する入力。 -/
lemma kanIsRelativeRightKanExtendedFrom_pathSection_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) :
    IsRelativeRightKanExtendedFrom (equivalencePathReplacementMap U) δ
      (F ≫ equivalencePathReplacementSection U) ↔ IsRelativeRightKanExtendedFrom U δ F := by
  have h := kanIsRelativeRightKanExtendedFrom_pathReplacement_iff U δ
    (F ≫ equivalencePathReplacementSection U)
  simpa only [Category.assoc, equivalencePathReplacementSection_projection,
    Category.comp_id] using h

end SerrePositivity.InfinityCategories.F1B

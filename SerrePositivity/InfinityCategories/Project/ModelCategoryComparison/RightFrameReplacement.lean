module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.RightFrameSpans

/-!
概要：同じ right frame の次数零を関手的な fibrant 置換として取り出す。
方針：元の全標的図式と augmentation を次数零で評価する。
規約：別の置換を選ばず、全対象 fibrant の仮定を置かない。
使われ方：一般モデル圏の三本矢の右脚を同じ fibrant 終域へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Limits HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy
open scoped _root_.Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ right frame の各値は fibrant。
方針：反対圏の同じ cofibrant 解像の各値を反転する。
規約：元の標的は任意。使われ方：右脚の全図式の Hom 不変性。 -/
lemma rightFrameDiagram_isFibrant (Y : C) (n : SimplexCategoryᵒᵖ) :
    IsFibrant (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).obj n) := by
  have hi : IsCofibrant ((r.obj.obj (op Y)).obj n.unop) :=
    (r.atObject (op Y)).isCofibrant_obj n.unop
  have hc : cofibrations Cᵒᵖ (initial.to ((r.obj.obj (op Y)).obj n.unop)) :=
    (cofibration_iff _).mp ((isCofibrant_iff _).mp hi)
  have : Fibration (initial.to ((r.obj.obj (op Y)).obj n.unop)).unop := ⟨hc⟩
  exact (isFibrant_iff_of_isTerminal
    (initial.to ((r.obj.obj (op Y)).obj n.unop)).unop initialIsInitial.unop).mpr inferInstance

/-- 概要：同じ right frame の次数零から元の fibrant 置換関手を作る。
方針：全標的関手を次数零で評価する。
規約：新しい置換を選ばない。使われ方：全右脚の一斉の fibrant 化。 -/
def rightFrameReplacement : C ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r ⋙ (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌)

/-- 概要：元の全標的から同じ次数零への全自然な単位。
方針：元の augmentation の次数零を読む。
規約：元の実射。使われ方：置換前後の三本矢の自然変換。 -/
def rightFrameReplacementUnit : 𝟭 C ⟶ rightFrameReplacement r where
  app Y := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app (op ⦋0⦌)
  naturality _ _ f := congr_app ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).naturality f) (op ⦋0⦌)

/-- 概要：同じ置換単位は自明 cofibration。
方針：元の augmentation の次数零の条件を使う。
規約：元の全標的で成立。使われ方：右脚の弱同値性と cofibrancy の保存。 -/
lemma rightFrameReplacementUnit_trivialCofibration (Y : C) :
    trivialCofibrations C ((rightFrameReplacementUnit r).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit_trivialCofibration r Y (op ⦋0⦌)

/-- 概要：同じ置換関手の値は fibrant。
方針：right frame の次数零の fibrancy を使う。
規約：元の標的は任意。使われ方：一般モデルの全右脚の比較。 -/
lemma rightFrameReplacement_isFibrant (Y : C) :
    IsFibrant ((rightFrameReplacement r).obj Y) :=
  rightFrameDiagram_isFibrant r Y (op ⦋0⦌)

/-- 概要：同じ置換関手は cofibrant 対象を cofibrant 対象へ送る。
方針：元の単位の cofibration 性を使う。
規約：底の cofibrancy を別途仮定しない。使われ方：cofibrant 相対圏内での置換。 -/
lemma rightFrameReplacement_isCofibrant (Y : C) [IsCofibrant Y] :
    IsCofibrant ((rightFrameReplacement r).obj Y) := by
  let i : Y ⟶ (rightFrameReplacement r).obj Y := (rightFrameReplacementUnit r).app Y
  have : Cofibration i :=
    ⟨(rightFrameReplacementUnit_trivialCofibration r Y).1⟩
  exact isCofibrant_of_cofibration i

/-- 概要：同じ置換関手は元の弱同値を保つ。
方針：元の単位の自然性と二対三を使う。
規約：全標的射で成立。使われ方：右脚の全図式の不変性。 -/
lemma rightFrameReplacement_map_weak {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences C ((rightFrameReplacement r).map f) := by
  apply (weakEquivalences C).of_precomp ((rightFrameReplacementUnit r).app Y) _
    (rightFrameReplacementUnit_trivialCofibration r Y).2
  rw [← (rightFrameReplacementUnit r).naturality f]
  exact (weakEquivalences C).comp_mem _ _ hf
    (rightFrameReplacementUnit_trivialCofibration r Z).2

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

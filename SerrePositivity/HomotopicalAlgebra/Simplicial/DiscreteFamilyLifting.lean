module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 各離散ファイバーのすべての単射に対する右持ち上げ性から全体の射影の右持ち上げ性を導く

## 概要
各離散ファイバーのすべての単射に対する右持ち上げ性から全体の射影の右持ち上げ性を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0392][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0392
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Fiberwise all-monomorphism lifting assembles over arbitrary discrete labels

The prescribed label can vary across the parameter. The resulting lift
retains that entire label map and every already specified simplex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.DiscreteFamily
variable {I : Type v} (F : I → SSet.{v})
  (hF : ∀ i, (MorphismProperty.monomorphisms SSet.{v}).rlp (terminal.from (F i)))

include hF in
lemma exists_extension {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (a : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total F) (b : V ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I)
    (hw : a ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.projection F = j ≫ b) :
    ∃ l : V ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total F, j ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.projection F = b := by
  have hl : ∀ i, ∃ l : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.obj b i ⟶ F i,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.map j b i ≫ l = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.extract F (j ≫ b) a hw i := by
    intro i
    have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.map j b i) (terminal.from (F i)) :=
      hF i _ inferInstance
    let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.extract F (j ≫ b) a hw i) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.map j b i)
        (terminal.from (F i)) (terminal.from (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.obj b i)) := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩
  let d := fun i => (hl i).choose
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.assemble F b d, ?_, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.assemble_projection F b d⟩
  ext n x
  let i := b.app n (j.app n x)
  have hf := types_congr_hom (congr_app (hl i).choose_spec n)
    (⟨x, rfl⟩ : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber.obj (j ≫ b) i).obj n)
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.assembleFn F b d n (j.app n x) = a.app n x
  calc
    _ = (⟨i, (d i).app n ⟨j.app n x, rfl⟩⟩ : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total F).obj n) := rfl
    _ = (⟨i, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.extract F (j ≫ b) a hw i).app n ⟨x, rfl⟩⟩ : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total F).obj n) :=
      congrArg (Sigma.mk i) hf
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.extractFn_spec F (j ≫ b) a hw i n ⟨x, rfl⟩

include hF in
/-- 各離散ファイバーのすべての単射に対する右持ち上げ性から全体の射影の右持ち上げ性を導く。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma projection_mono_rlp :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.projection F) := by
  intro U V j hj
  have : Mono j := hj
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨l, hl, hp⟩ := exists_extension F hF j a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := hp }⟩⟩

include hF in
lemma projection_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.projection F)) :=
  MonoRightLiftingContraction.localized_isIso _ (projection_mono_rlp F hF)

end SerrePositivity.SimplicialModel.DiscreteFamily

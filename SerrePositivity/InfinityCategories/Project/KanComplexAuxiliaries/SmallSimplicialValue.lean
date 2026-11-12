module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# 各次数の小ささが証明済みの図式を小さい値宇宙へ移し元のliftと自然同型で結ぶ

## 概要
各次数の小ささが証明済みの図式を小さい値宇宙へ移し元のliftと自然同型で結ぶ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
各次数の小ささは証明済みの入力であり、ホモトピー的な小ささだけから推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0575][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0575
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Shrinking a simplicial value whose degrees have already been proved small

The inverse equivalences define every simplicial operator, so this retains
all face and degeneracy identities. No homotopical smallness assumption is substituted.
-/

@[expose] public section
universe v w uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable (X : SSet.{max w v}) (hX : ∀ n, Small.{v} (X.obj n))

def shrink : SSet.{v} := by
  letI : FunctorToTypes.Small.{v} X := hX
  exact FunctorToTypes.shrink X

def liftIso : SSet.uliftFunctor.{max w v, v}.obj (shrink X hX) ≅ X := by
  letI : FunctorToTypes.Small.{v} X := hX
  exact NatIso.ofComponents
    (fun n => (Equiv.ulift.trans (equivShrink.{v} (X.obj n)).symm).toIso) (by
      intro n m f
      ext x
      change (equivShrink.{v} (X.obj m)).symm
          (equivShrink.{v} (X.obj m) (X.map f ((equivShrink.{v} (X.obj n)).symm x.down))) = _
      exact (equivShrink.{v} (X.obj m)).symm_apply_apply _)

variable {D : Type uD} [Category.{vD} D]
  (F : D ⥤ SSet.{max w v}) (hF : ∀ d n, Small.{v} ((F.obj d).obj n))

/-- All base morphisms are shrunk simultaneously. The base category may be large. -/
def shrinkDiagram : D ⥤ SSet.{v} where
  obj d := shrink (F.obj d) (hF d)
  map {d e} f := by
    letI : FunctorToTypes.Small.{v} (F.obj d) := hF d
    letI : FunctorToTypes.Small.{v} (F.obj e) := hF e
    exact FunctorToTypes.shrinkMap (F.map f)
  map_id d := by
    ext n x
    change equivShrink _ ((F.map (𝟙 d)).app n ((equivShrink _).symm x)) = x
    rw [F.map_id]
    exact (equivShrink _).apply_symm_apply x
  map_comp f g := by
    ext n x
    change equivShrink _ ((F.map (f ≫ g)).app n ((equivShrink _).symm x)) = _
    rw [F.map_comp]
    exact (congrArg (equivShrink _) (congrArg ((F.map g).app n)
      ((equivShrink _).symm_apply_apply _))).symm

/-- 各次数の小ささが証明済みの図式を小さい値宇宙へ移し元のliftと自然同型で結ぶ。

各次数の小ささは証明済みの入力であり、ホモトピー的な小ささだけから推論しない。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def diagramLiftIso : shrinkDiagram F hF ⋙ SSet.uliftFunctor.{max w v, v} ≅ F :=
  NatIso.ofComponents (fun d => liftIso (F.obj d) (hF d)) (by
    intro d e f
    ext n x
    change (equivShrink _).symm
        (equivShrink _ ((F.map f).app n ((equivShrink _).symm x.down))) = _
    exact (equivShrink _).symm_apply_apply _)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

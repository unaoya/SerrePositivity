module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorTargetTransport
public import SerrePositivity.EInfinity.Hammock.UnmarkedPrefixHammock
public import SerrePositivity.EInfinity.Hammock.WordCutFactorColumns

/-!
# 元の最初の切断の依存和の点

概要：最初の非指定生成矢・実際の指定 prefix・残りの hammock の像を束ねる。
方針：既存の選択された全図式を同じ二つの余極限の標準射へ送る。
規約：prefix は元の指定部分圏の W-hammock の点である。
使われ方：一段の切断を単体集合の射にする。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ [])

def generator : FactorTarget.Index W :=
  ⟨rowGenerator W τ (AttachedPrefix.index W τ h) (AttachedPrefix.nonempty W τ h),
    (fixedRowCut W τ (AttachedPrefix.index W τ h) (AttachedPrefix.nonempty W τ h) 0).unmarked⟩

def leftPoint : (FactorTarget.left W X (generator W τ h).val).obj n :=
  (graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths))
    (⟨X⟩ : WideSubcategory W.paths) ⟨(generator W τ h).val.left⟩
    (prefixWord w (AttachedPrefix.index W τ h))).app n (AttachedPrefix.markedSimplex W τ h)

def rightPoint : (FactorTarget.right W Y (generator W τ h).val).obj n :=
  (graphInclusion W.paths (generator W τ h).val.right Y
    (residualWord w (AttachedPrefix.index W τ h))).app n
      (Attachments.residualFunctor W τ (AttachedPrefix.index W τ h)
        (AttachedPrefix.nonempty W τ h))

def point : (FactorTarget.space W X Y).obj n :=
  ⟨generator W τ h, leftPoint W τ h, rightPoint W τ h⟩

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor

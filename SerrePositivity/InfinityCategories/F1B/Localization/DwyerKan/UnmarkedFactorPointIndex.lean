module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFactorPoint

/-!
# 同じ最初の列の表示による切断点の回収

概要：全指定 prefix の証明と最初の列の位置を選び直しても同じ切断点を得る。
方針：位置の等式で帰納し、元の図式と持ち上げの証明独立性を使う。
規約：実際の指定部分圏の余極限の点を保持する。
使われ方：語の作用後の像の最小列から標準の切断点への回収。
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
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length) (hi : column W (τ.obj 0) i ≠ [])
  (hm : ∀ d k, W.paths (((Attachments.prefixDiagram W τ i hi).obj d).arrow k))

def pointAt : (FactorTarget.space W X Y).obj n :=
  ⟨⟨rowGenerator W τ i hi, (fixedRowCut W τ i hi 0).unmarked⟩,
    (graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths))
      (⟨X⟩ : WideSubcategory W.paths) ⟨(rowGenerator W τ i hi).left⟩ (prefixWord w i)).app n
        (MarkedZigzag.liftFunctor W.paths (Attachments.prefixFunctor W τ i hi) hm),
    (graphInclusion W.paths (rowGenerator W τ i hi).right Y (residualWord w i)).app n
      (Attachments.residualFunctor W τ i hi)⟩

lemma pointAt_eq (h : ∃ j, column W (τ.obj 0) j ≠ []) (he : i = AttachedPrefix.index W τ h) :
    pointAt W τ i hi hm = point W τ h := by
  cases he
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor

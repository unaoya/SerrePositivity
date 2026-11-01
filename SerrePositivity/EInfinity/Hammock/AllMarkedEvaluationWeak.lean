module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverEvaluationWeak
public import SerrePositivity.EInfinity.Hammock.TopEquivalenceWeak
public import SerrePositivity.EInfinity.Hammock.HammockValueRelative
public import SerrePositivity.EInfinity.Hammock.AllMarkedNative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedGeneratorCategory

/-!
# 元の指定部分圏の hammock の自由 groupoid への評価の弱同値性

概要：元の自由圏の指定部分圏の実際の hammock 評価自身は弱同値。
方針：指定生成圏との元の圏同値と同じ評価の合成則で自由圏の結論を移す。
規約：W の乗法性や可縮性の追加入力は不要。
使われ方：元の自由積分解の指定因子の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def nativeFreeEvaluation :
    WideSubcategory W.paths ⥤ Quiver.FreeGroupoid (MarkedGenerators.quiver W) :=
  MarkedGenerators.fromWide W ⋙ FreeQuiverCover.positiveEvaluation

lemma nativeFreeEvaluation_inverts_top :
    (⊤ : MorphismProperty (WideSubcategory W.paths)).IsInvertedBy (nativeFreeEvaluation W) := by
  intro X Y f _
  infer_instance

def nativeValue (X Y : Paths C) : nativeSpace W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((nativeFreeEvaluation W).obj ⟨X⟩ ⟶ (nativeFreeEvaluation W).obj ⟨Y⟩) :=
  Zigzag.Value.colimitValue (nativeFreeEvaluation W) (nativeFreeEvaluation_inverts_top W) ⟨X⟩ ⟨Y⟩

lemma nativeValue_isWeakHomotopyEquivalence (X Y : Paths C) :
    IsWeakHomotopyEquivalence (nativeValue W X Y) := by
  have he := topEquivalence_colimitMap_weak (MarkedGenerators.equivalence W).symm
    (⟨X⟩ : WideSubcategory W.paths) ⟨Y⟩
  have hv := FreeQuiverCover.existingHammockValue_isWeakHomotopyEquivalence
    (Q := MarkedGenerators.quiver W) X Y
  have hc := he.comp hv
  have hn : Relative.colimitMap (topRelative (MarkedGenerators.fromWide W))
      (⟨X⟩ : WideSubcategory W.paths) ⟨Y⟩ ≫
        Zigzag.Value.colimitValue
          (FreeQuiverCover.positiveEvaluation (Q := MarkedGenerators.quiver W))
          FreeQuiverCover.positiveEvaluation_inverts_top X Y = nativeValue W X Y := by
    exact Zigzag.Value.colimitValue_relative (topRelative (MarkedGenerators.fromWide W))
      FreeQuiverCover.positiveEvaluation FreeQuiverCover.positiveEvaluation_inverts_top
      (⟨X⟩ : WideSubcategory W.paths) ⟨Y⟩
  exact (congrArg IsWeakHomotopyEquivalence hn).mp hc

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked

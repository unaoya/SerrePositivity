module

public import SerrePositivity.KST.Comparison.HomologyMorphismProperty

/-!
# 関手による逆像と余極限閉性

概要：余極限を保存する関手で引き戻した射の性質の閉性を証明する。
方針：指定した余極限余錐を関手で送り、標的圏の閉性を適用する。
規約：Waldhausen LNM 1126 §1.7・§1.8 の基底上のセル添付に用いる一般補題。
使われ方：局所係数ホモロジー同型と台の単射性の余積閉性。
-/

@[expose] public section
noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：余極限閉な射の性質の逆像も、関手が保存する形の余極限で閉じる。
方針：余極限余錐とその間の可換な射を関手で送る。
規約：圏と添字の宇宙を独立にする。
使われ方：基底上の局所係数の閉性の移送。
-/
theorem morphismProperty_inverseImage_stableColimits
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty D) (K : C ⥤ D)
    (J : Type u₃) [Category.{v₃} J]
    [W.IsStableUnderColimitsOfShape J] [PreservesColimitsOfShape J K] :
    (W.inverseImage K).IsStableUnderColimitsOfShape J where
  condition F G cF cG hcF hcG α hα f hf := by
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := W) (F ⋙ K) (G ⋙ K) (K.mapCocone cF) (K.mapCocone cG)
      (isColimitOfPreserves K hcF) (isColimitOfPreserves K hcG)
      (Functor.whiskerRight α K) hα (K.map f) (fun j => by
        change K.map (cF.ι.app j) ≫ K.map f =
          K.map (α.app j) ≫ K.map (cG.ι.app j)
        rw [← K.map_comp, ← K.map_comp, hf j])

end SerrePositivity.KST.Comparison

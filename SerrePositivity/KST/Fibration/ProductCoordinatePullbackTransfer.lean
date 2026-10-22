module
public import SerrePositivity.KST.Fibration.ProductCoefficientHomotopyPullback

/-! # 元の第一射影を保つ積座標からのホモトピー引き戻しの移送 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 積比較の第二成分を元の縦射に沿って引き戻した射対は、厳密な比較立方体を作る。 -/
theorem isHomotopyPullback_of_productCoordinates
    {P X Y B K : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g) (c : Y ⟶ B ⊗ K) (hc : c ≫ fst _ _ = g)
    (hciso : IsIso (AnodyneHomotopy.anodyneQ.map c))
    (hpiso : IsIso (AnodyneHomotopy.anodyneQ.map (lift a (b ≫ c ≫ snd _ _)))) :
    IsHomotopyPullback sq := by
  apply (isHomotopyPullback_iff_of_localized_isIso sq
    (productPullbackSquare f K).toCommSq (lift a (b ≫ c ≫ snd _ _))
    (𝟙 X) c (𝟙 B) ?_ ?_ ?_ ?_ hpiso (by infer_instance) hciso
      (by infer_instance)).mpr
  · exact productPullback_isHomotopyPullback f K
  · rw [Category.comp_id, lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hc, Category.assoc, whiskerRight_fst,
        ← Category.assoc, lift_fst]
      exact sq.w.symm
    · simp only [Category.assoc, whiskerRight_snd, lift_snd]
  · simp only [Category.comp_id, Category.id_comp]
  · exact (Category.comp_id g).trans hc.symm

end SerrePositivity.KST.Fibration

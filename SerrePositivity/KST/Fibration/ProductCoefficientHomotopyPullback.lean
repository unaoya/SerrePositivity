module
public import SerrePositivity.KST.Comparison.ProductHomotopyPullback
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-! # 元の係数写像が局所化同型である Cartesian 積座標のホモトピー引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の二成分の実写像と元の第一射影による厳密な可換四角形。 -/
theorem productCoefficientSquare {X Y A B : SSet.{u}} (f : X ⟶ Y) (k : A ⟶ B) :
    CommSq (fst X A) (f ⊗ₘ k) f (fst Y B) := ⟨(tensorHom_fst f k).symm⟩

/-- 元の係数写像が局所化同型なら、元の第一射影の四角形そのものは homotopy pullback。 -/
theorem productCoefficientSquare_homotopyPullback {X Y A B : SSet.{u}}
    (f : X ⟶ Y) (k : A ⟶ B) (hk : IsIso (AnodyneHomotopy.anodyneQ.map k)) :
    IsHomotopyPullback (productCoefficientSquare f k) := by
  have hP := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso k hk X
  apply (isHomotopyPullback_iff_of_localized_isIso
    (productCoefficientSquare f k) (productPullbackSquare f B).toCommSq
    (X ◁ k) (𝟙 X) (𝟙 (Y ⊗ B)) (𝟙 Y)
    ?_ ?_ ?_ ?_ hP (by infer_instance) (by infer_instance) (by infer_instance)).mpr
  · exact productPullback_isHomotopyPullback f B
  · rw [Category.comp_id, whiskerLeft_fst]
  · rw [Category.comp_id, tensorHom_def']
  · simp only [Category.comp_id, Category.id_comp]
  · simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.KST.Fibration

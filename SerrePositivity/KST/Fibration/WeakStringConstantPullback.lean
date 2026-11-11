module
public import SerrePositivity.KST.Fibration.WeakStringZeroRow
public import SerrePositivity.KST.Fibration.WeakStringPostRealizationPullback

/-! # 元の定数 W 列包含と Verdier 包含による後合成のホモトピー引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の零行と入力の実現の同型は、元の包含側の完全関手と厳密に可換。 -/
lemma weakStringRealizationZeroRowIso_postcomp (F : StableModel.{u} ⥤ SSet.{u})
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (F.map (weakStringPostExact f q ⦋0⦌) ▷ Δ[0]) ≫
        (weakStringRealizationZeroRowIso F q).hom =
      (weakStringRealizationZeroRowIso F (f ≫ q : A ⟶ C)).hom ≫
        F.map (sInputExactMap f) := by
  change (F.map (weakStringPostExact f q ⦋0⦌) ▷ Δ[0]) ≫
      (fst _ _ ≫ F.map (weakStringZeroAmbientIso q).hom) =
    (fst _ _ ≫ F.map (weakStringZeroAmbientIso (f ≫ q : A ⟶ C)).hom) ≫ _
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, ← F.map_comp,
    weakStringZeroAmbientIso_postcomp, F.map_comp, Category.assoc]

/-- 元の定数包含・入力の実完全関手・対角の後合成を保つ可換四角形。 -/
theorem weakStringConstantPostSquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    CommSq
      (weakStringRealizationConstantDiagonal (multiRealizationFunctor r) (f ≫ q : A ⟶ C))
      ((multiRealizationFunctor r).map (sInputExactMap f))
      (simplicialDiagonalFunctor.map (weakStringMultiPostcomp f q r))
      (weakStringRealizationConstantDiagonal (multiRealizationFunctor r) q) :=
  ⟨(weakStringRealizationConstantDiagonal_postcomp (multiRealizationFunctor r) f q).symm⟩

/-- Verdier 列では、元の入力と定数 W 列包含の四角形は全正反復で homotopy pullback。 -/
theorem weakStringConstantPostSquare_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ) :
    IsHomotopyPullback (weakStringConstantPostSquare i q (r + 1)) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk (diagonalRowEvaluation_naturality
      (weakStringMultiPostcomp i q (r + 1)) 0).symm)
    (weakStringConstantPostSquare i q (r + 1))
    (weakStringRealizationZeroRowIso (multiRealizationFunctor (r + 1))
      (i ≫ q : A ⟶ C)).hom (𝟙 _)
    (weakStringRealizationZeroRowIso (multiRealizationFunctor (r + 1)) q).hom (𝟙 _)
    ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance)
    (by infer_instance) (by infer_instance)).mp
  · exact weakStringMultiPostcomp_realization_homotopyPullback h r 0
  · rw [Category.comp_id]
    exact weakStringRealizationZeroRow_evaluation _ _
  · exact weakStringRealizationZeroRowIso_postcomp _ _ _
  · simp only [Category.comp_id, Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact weakStringRealizationZeroRow_evaluation _ _

end SerrePositivity.KST.Fibration

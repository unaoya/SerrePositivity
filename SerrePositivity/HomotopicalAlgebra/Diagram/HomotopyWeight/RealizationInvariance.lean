module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroNaturality
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Localizations.LocalizationDetection
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 射影 cofibrant 重みによる frame の実現の弱同値不変性

概要：Hovey §5.4 の重み付き実現は係数 frame の頂点ごとの弱同値を保つ。
方針：錐の π₀ の不変性を元の実現対象からの Hom の全単射へ移す。
規約：図式の射影 cofibrancy や単体集合のモデル構造は要求しない。
使われ方：実際の E 代数の一般 homotopy 極限の擬同型不変性。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))

include hW

/-- 概要：係数 frame の弱同値は同じ重みの実現の弱同値になる（Hovey §5.4）。
方針：自然な錐の π₀ 比較と fibrant 終域の局所化 Hom による検出を使う。
規約：各 frame は Reedy cofibrant かつ homotopically constant とする。
使われ方：小図式の右 frame の end の擬同型不変性。 -/
lemma realization_map_frame_weakEquivalence
    (fact : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    {B B' : K ⥤ SimplexCategory ⥤ C} (a : B ⟶ B')
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    (hB' : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B'.obj k)))
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B.obj k).map f))
    (hconst' : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B'.obj k).map f))
    (ha : ∀ k n, weakEquivalences C ((a.app k).app n)) :
    weakEquivalences C ((FrameWeightRealization.map K a).app W) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.weakEquivalence_of_localized_precomposition_fibrant
  dsimp only
  intro Y hY
  have := hY
  let Q := (weakEquivalences C).Q
  let p := (WeightedCones.coneSpace Kᵒᵖ W).map
    (((FrameWeightRealization.homFamily K).map a.op).app Y)
  have hp : Function.Bijective (SSet.mapπ₀ p) := by
    have hi := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_source_weakEquivalence_isIso K W hW SSet.π₀Functor
      _root_.SerrePositivity.SimplicialModel.PiZeroLocalization.inverts_anodyne fact a hB hB' ha Y
    exact (CategoryTheory.isIso_iff_bijective _).mp hi
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Y
  let e' := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B' hW hB' hconst' Q Y
  have hn (z) : e (SSet.mapπ₀ p z) = Q.map ((FrameWeightRealization.map K a).app W) ≫
      e' z := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_source K W hW hB hB' hconst hconst' Q a Y z
  have hb := e.bijective.comp (hp.comp e'.symm.bijective)
  simpa only [Function.comp_def, hn, Equiv.apply_symm_apply] using hb

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

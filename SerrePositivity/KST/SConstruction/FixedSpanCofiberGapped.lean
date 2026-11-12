module
public import SerrePositivity.KST.SConstruction.CofiberCompletionGapped

/-! # span を固定した cofiber 族から gapped 図式へ
概要：既存の相対補完が保持する枠と span の等号から実際の右上角の図式の gapped 性を導く。
方針：uncurry で入力を形状の等号に戻し、正方形の比較を通じて押し出し性を移す。
規約：出力の gapped 性は仮定しない。
使われ方：BGT Lemma 7.3 の零次元の存在と正次元の相対性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：固定した span の族の等号は積上の図式でも入力の厳密な等号になる。
方針：uncurry の前合成の自然性と二因子の交換則を使う。
規約：quasicategory 性は不要。使われ方：比較 prism の入力条件。 -/
lemma arSquareFamilyDiagram_span {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary) ≫ arSquareFamilyDiagram H = arCofiberSpanMap n ≫ F := by
  dsimp only [arSquareFamilyDiagram]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right,
    Category.assoc, ← uncurry_pre_app, h, frameCofiberSpanFamily, uncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：固定 span の等号は固定零射の等号を含む。
方針：第二辺へ制限する。
規約：厳密等号。使われ方：第二端点の比較 prism。 -/
lemma arSquareFamilyDiagram_left {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ arSquareFamilyDiagram H = arCofiberZeroInputMap n ≫ F := by
  have he := congrArg (fun p => (arNerve n ◁ horn₂₀.ι₀₂) ≫ p)
    (arSquareFamilyDiagram_span H F h)
  simp only [← Category.assoc, ← whiskerLeft_comp] at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge, arCofiberSpanMap_right] at he
  exact he

/-- 概要：固定 span の等号は固定入力射の等号を含む。
方針：第一辺へ制限する。
規約：厳密等号。使われ方：第一端点の比較 prism。 -/
lemma arSquareFamilyDiagram_bottom {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (F : frameNerve n ⟶ C)
    (h : H ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = frameCofiberSpanFamily F) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ arSquareFamilyDiagram H = arCofiberInputMap n ≫ F := by
  have he := congrArg (fun p => (arNerve n ◁ horn₂₀.ι₀₁) ≫ p)
    (arSquareFamilyDiagram_span H F h)
  simp only [← Category.assoc, ← whiskerLeft_comp] at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, arCofiberSpanMap_left] at he
  exact he

/-- 概要：積上の族の各パラメーターでの正方形は元の関手頂点を復号したもの。
方針：curry の頂点評価と逆律を使う。
規約：厳密等号。使われ方：cofiber の全部分複体の普遍性を適用する。 -/
lemma arSquareFamilyDiagram_at {n : ℕ} {C : SSet.{u}}
    (H : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) (a : Ar.{u} n) :
    lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫
      arSquareFamilyDiagram H =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) C).symm
          (H.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a)) := by
  have he := curry_vertex_value (uncurry H) (ComposableArrows.mk₀ a)
  rw [curry_uncurry] at he
  change H.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (SSet.const (ComposableArrows.mk₀ a))
      (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ arSquareFamilyDiagram H) at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).injective
  rw [Equiv.apply_symm_apply]
  exact he.symm

/-- 概要：枠と全 span を固定する cofiber の族の右上角の実際の図式は gapped。
方針：族の頂点の押し出し性を三つの prism の比較で標準正方形へ移す。
規約：C は quasicategory。安定性は補完の存在にのみ使い、この含意には不要。
使われ方：第一行復元の存在証明の最後の普遍性。 -/
lemma isGapped_cofiberFamily_of_fixed_span {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (H : arNerve n ⟶ cofiberDiagrams C) (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (hframe : frameInclusion n ≫ H = zeroFrameCofiberFamily F hF)
    (hspan : H ≫ cofiberSpan C = frameCofiberSpanFamily F) :
    IsGapped (H ≫ cofiberApex C) := by
  let R := H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
  have hf : frameInclusion n ≫ R = frameCofiberFamily F := by
    dsimp only [R]
    rw [← Category.assoc, hframe, zeroFrameCofiberFamily_ι]
  have hs : R ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = frameCofiberSpanFamily F := hspan
  have hg := isGapped_arSquareFamilyApex (arSquareFamilyDiagram R) F hF
    (arSquareFamilyDiagram_frame R F hf) (arSquareFamilyDiagram_left R F hs)
    (arSquareFamilyDiagram_bottom R F hs) (by
      intro a
      rw [arSquareFamilyDiagram_at]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
        (H.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))).2)
  have he := arSquareFamilyDiagram_evaluate R
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  exact he ▸ hg

end SerrePositivity.KST.SConstruction

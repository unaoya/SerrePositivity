module
public import SerrePositivity.KST.SConstruction.FixedSpanCofiberGapped

/-! # 零対角の枠の gapped 延長
概要：任意の零対角の枠を gapped な Ar[n] 図式へ厳密に延長する。
方針：枠を指定境界として全 span の cofiber 補完を行い、gapped 性の判定を適用する。
規約：安定性は cofiber 補完の存在に使う。
使われ方：BGT Lemma 7.3 の零次元の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：枠の標準 cofiber 族の span は全 span 入力の枠への制限。
方針：uncurry で二変数を開き、span の形状の等号を使う。
規約：quasicategory 性は不要。使われ方：相対 cofiber 補完の境界条件。 -/
lemma frameCofiberFamily_span {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    frameCofiberFamily F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C =
      frameInclusion n ≫ frameCofiberSpanFamily F := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ frameNerve n) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫ frameCofiberSquareMap n =
      ((horn 2 0 : SSet.{u}) ◁ frameInclusion n) ≫
        (β_ (horn 2 0 : SSet.{u}) (arNerve n)).hom ≫ arCofiberSpanMap n := by
    rw [BraidedCategory.braiding_naturality_left_assoc, frameCofiberSquareMap_span,
      BraidedCategory.braiding_naturality_right_assoc]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, frameCofiberFamily, frameCofiberSpanFamily,
    uncurry_curry, uncurry_curry]
  simpa only [Category.assoc] using congrArg (fun p => p ≫ F) he

/-- 概要：零対角の枠を、全 span を固定した cofiber の族へ厳密に延長できる。
方針：枠包含を指定単射として相対 cofiber 補完を適用する。
規約：C は安定な quasicategory。使われ方：零次元における gapped 図式の存在。 -/
lemma exists_cofiberFamily_of_zeroFrame {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    ∃ H : arNerve n ⟶ cofiberDiagrams C,
      frameInclusion n ≫ H = zeroFrameCofiberFamily F hF ∧
      H ≫ cofiberSpan C = frameCofiberSpanFamily F := by
  have hd : ∀ v : (arNerve n) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌)
        ((frameCofiberSpanFamily F).app (Opposite.op ⦋0⦌) v)) := by
    intro v
    obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective v
    exact frameCofiberSpanFamily_zero F hF a
  apply exists_relative_cofiberFamily_over_span (frameInclusion n) (frameCofiberSpanFamily F)
    hd (zeroFrameCofiberFamily F hF)
  rw [cofiberSpan, ← Category.assoc, zeroFrameCofiberFamily_ι]
  exact frameCofiberFamily_span F

/-- 概要：零対角の任意の枠は実際の gapped 図式へ厳密に延長できる。
方針：固定 span の cofiber 族の右上角を取り、gapped 性と枠の回収を証明する。
規約：C は安定な quasicategory。出力の普遍性を仮定しない。
使われ方：第一行制限の零次元の持ち上げ。 -/
lemma exists_gapped_extension_of_zeroFrame {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : frameNerve n ⟶ C) (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    ∃ G : arNerve n ⟶ C, IsGapped G ∧ frameInclusion n ≫ G = F := by
  obtain ⟨H, hframe, hspan⟩ := exists_cofiberFamily_of_zeroFrame F hF
  refine ⟨H ≫ cofiberApex C, isGapped_cofiberFamily_of_fixed_span H F hF hframe hspan, ?_⟩
  rw [← Category.assoc, hframe, zeroFrameCofiberFamily_apex]

end SerrePositivity.KST.SConstruction

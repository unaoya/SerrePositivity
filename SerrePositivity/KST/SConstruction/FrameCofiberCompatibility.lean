module
public import SerrePositivity.KST.SConstruction.FrameCofiberFamiliesMap

/-! # 枠の cofiber 族と全区間の族の一致
概要：枠からの cofiber 抽出は gapped 境界の抽出と厳密に一致する。
方針：内部 currying の第二変数の自然性と、枠内の正方形の包含式を用いる。
規約：HTT §4.3.2 の相対補完で第一行を厳密に保持する。
使われ方：BGT Lemma 7.3 の境界と枠を同時に固定した持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 currying は第二変数での前合成に自然。
方針：関手単体集合の二つの内部 Hom の成分を計算する。
規約：全ての単体集合で成立。使われ方：枠への制限との可換性。 -/
lemma ihomCurry_pre_whiskerLeft {A B : SSet.{u}} (f : A ⟶ B) (K X : SSet.{u}) :
    (pre (K ◁ f)).app X ≫ (ihomCurryIso K A X).hom =
      (ihomCurryIso K B X).hom ≫ (pre f).app ((ihom K).obj X) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro k
  change F.app t (α ≫ β) (k, f.app t (A.map β a)) =
    F.app t (α ≫ β) (k, B.map β (f.app e a))
  exact congrArg (fun b => F.app t (α ≫ β) (k, b))
    (ConcreteCategory.congr_hom (f.naturality β) a)

/-- 概要：Ar[n] の cofiber 抽出を枠に制限すると枠の抽出に一致する。
方針：第二変数での内部 currying の自然性と枠の添字写像の包含式を使う。
規約：gapped 条件は不要。使われ方：指定境界との厳密な接続。 -/
lemma arCofiberFamilyOperator_frame (n : ℕ) (C : SSet.{u}) :
    arCofiberFamilyOperator n C ≫
      (pre (frameInclusion n)).app ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) =
      (pre (frameInclusion n)).app C ≫ frameCofiberFamilyOperator n C := by
  have he : ((Δ[1] ⊗ Δ[1] : SSet.{u}) ◁ frameInclusion n) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberSquareMap n =
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫
        frameCofiberSquareMap n ≫ frameInclusion n := by
    rw [BraidedCategory.braiding_naturality_right_assoc, ← frameCofiberSquareMap_inclusion]
  dsimp only [arCofiberFamilyOperator, frameCofiberFamilyOperator]
  rw [Category.assoc, ← ihomCurry_pre_whiskerLeft]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  simp only [Category.assoc] at ⊢
  rw [he]

/-- 概要：枠上の cofiber 族は指定された gapped 族の枠への制限に等しい。
方針：条件を忘れる単射の後で、抽出作用素の枠への制限の等号を使う。
規約：C は quasicategory。使われ方：境界と枠を同時に指定する持ち上げ。 -/
lemma gappedCofiberFamiliesMap_frame (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    gappedCofiberFamiliesMap n C ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
      gappedFrameRestriction n C ≫ zeroFrameCofiberFamiliesMap n C := by
  apply (cancel_mono ((ihom (frameNerve n)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)).1
  rw [Category.assoc, ← (pre (frameInclusion n)).naturality,
    ← Category.assoc, gappedCofiberFamiliesMap_ι, Category.assoc,
    arCofiberFamilyOperator_frame, ← Category.assoc, ← gappedFrameRestriction_ι,
    Category.assoc, ← zeroFrameCofiberFamiliesMap_ι]
  simp only [Category.assoc]

/-- 概要：枠内の標準正方形の下辺は、元の第一行の入力である。
方針：縦座標を零にした鎖の各頂点を計算する。
規約：全次数での厳密等号。使われ方：cofiber 族の入力と枠の指定の両立。 -/
lemma frameCofiberSquareMap_bottom (n : ℕ) :
    (frameNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫ frameCofiberSquareMap.{u} n =
      (frameInclusion n ▷ (Δ[1] : SSet.{u})) ≫ arCofiberInputMap n := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rfl

/-- 概要：枠の cofiber 抽出の入力は全第一行入力の枠への制限。
方針：内部 currying の両変数の自然性と下辺の形状の等号を使う。
規約：零対角条件は不要。使われ方：相対 cofiber 補完の基底との可換性。 -/
lemma frameCofiberFamilyOperator_input (n : ℕ) (C : SSet.{u}) :
    frameCofiberFamilyOperator n C ≫ (ihom (frameNerve n)).map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C) =
      frameCofiberInputOperator n C ≫
        (pre (frameInclusion n)).app ((ihom (Δ[1] : SSet.{u})).obj C) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ▷ frameNerve n) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫ frameCofiberSquareMap n =
      ((Δ[1] : SSet.{u}) ◁ frameInclusion n) ≫
        (β_ (Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberInputMap n := by
    rw [BraidedCategory.braiding_naturality_left_assoc, frameCofiberSquareMap_bottom,
      BraidedCategory.braiding_naturality_right_assoc]
  dsimp only [frameCofiberFamilyOperator, frameCofiberInputOperator]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ihomCurry_pre_whiskerRight,
    Category.assoc, ← ihomCurry_pre_whiskerLeft]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  simp only [Category.assoc] at ⊢
  rw [he]

/-- 概要：零対角の枠上の cofiber 族は、入力の指定と厳密に両立する。
方針：全部分複体への包含後の式と抽出作用素の入力の等号を使う。
規約：C は quasicategory。使われ方：相対持ち上げ問題の可換正方形。 -/
lemma zeroFrameCofiberFamiliesMap_input (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map (cofiberProjection C) =
      frameCofiberInputs n C ≫
        (pre (frameInclusion n)).app ((ihom (Δ[1] : SSet.{u})).obj C) := by
  rw [cofiberProjection, Functor.map_comp, ← Category.assoc,
    zeroFrameCofiberFamiliesMap_ι, Category.assoc, frameCofiberFamilyOperator_input]
  rfl

end SerrePositivity.KST.SConstruction

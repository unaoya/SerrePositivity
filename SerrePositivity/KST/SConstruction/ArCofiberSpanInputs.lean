module
public import SerrePositivity.KST.SConstruction.ArCofiberSpanShape
public import SerrePositivity.KST.SConstruction.FramePreservingCompletion

/-! # 枠の span 入力と cofiber 抽出の両立
概要：枠から取り出した span を関手単体集合の族にし、既存 gapped 図式の抽出と照合する。
方針：内部 currying の自然性と二辺の形状写像の厳密な等号を使う。
規約：入力の零角だけでなく零射も保持する。
使われ方：BGT Lemma 7.3 の相対的な cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：枠の図式から全区間の span の族を取る作用素。
方針：span の形状で前合成して内部 curry を取る。
規約：零条件を課す前の作用素。使われ方：cofiber の完全な入力。 -/
def frameCofiberSpanOperator (n : ℕ) (C : SSet.{u}) :
    (ihom (frameNerve n)).obj C ⟶
      (ihom (arNerve n)).obj ((ihom (horn 2 0 : SSet.{u})).obj C) :=
  (pre ((β_ (horn 2 0 : SSet.{u}) (arNerve n)).hom ≫ arCofiberSpanMap n)).app C ≫
    (ihomCurryIso (horn 2 0 : SSet.{u}) (arNerve n) C).hom

/-- 概要：cofiber の自然な抽出を span に制限すると枠の入力作用素。
方針：第一変数での curry の自然性と span の形状の等号を使う。
規約：gapped 条件は不要。使われ方：指定境界の入力の一致。 -/
lemma arCofiberFamilyOperator_span (n : ℕ) (C : SSet.{u}) :
    arCofiberFamilyOperator n C ≫ (ihom (arNerve n)).map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C) =
      (pre (frameInclusion n)).app C ≫ frameCofiberSpanOperator n C := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ arNerve n ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom) ≫ arCofiberSquareMap n =
      ((β_ (horn 2 0 : SSet.{u}) (arNerve n)).hom ≫ arCofiberSpanMap n) ≫
        frameInclusion n := by
    rw [BraidedCategory.braiding_naturality_left, Category.assoc,
      arCofiberSquareMap_span, ← Category.assoc]
  dsimp only [arCofiberFamilyOperator, frameCofiberSpanOperator]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ihomCurry_pre_whiskerRight]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rw [he]

/-- 概要：枠の四角形の span は全区間の入力の枠への制限。
方針：枠の包含後で二因子の交換則と Ar[n] の span の式を使う。
規約：形状の厳密な等号。使われ方：枠上の入力の照合。 -/
lemma frameCofiberSquareMap_span (n : ℕ) :
    (frameNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary) ≫ frameCofiberSquareMap.{u} n =
      (frameInclusion n ▷ (horn 2 0 : SSet.{u})) ≫ arCofiberSpanMap n := by
  apply (cancel_mono (frameInclusion n)).1
  rw [Category.assoc, frameCofiberSquareMap_inclusion, ← Category.assoc,
    whisker_exchange, Category.assoc, arCofiberSquareMap_span, ← Category.assoc]

/-- 概要：枠上の cofiber 抽出の span は、全区間の入力の枠への制限。
方針：内部 currying の両変数の自然性と span の形状の等号を使う。
規約：零対角条件は不要。使われ方：枠を同時に固定する相対内部 Hom。 -/
lemma frameCofiberFamilyOperator_span (n : ℕ) (C : SSet.{u}) :
    frameCofiberFamilyOperator n C ≫
      (ihom (frameNerve n)).map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C) =
      frameCofiberSpanOperator n C ≫
        (pre (frameInclusion n)).app ((ihom (horn 2 0 : SSet.{u})).obj C) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ frameNerve n) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫ frameCofiberSquareMap n =
      ((horn 2 0 : SSet.{u}) ◁ frameInclusion n) ≫
        (β_ (horn 2 0 : SSet.{u}) (arNerve n)).hom ≫ arCofiberSpanMap n := by
    rw [BraidedCategory.braiding_naturality_left_assoc, frameCofiberSquareMap_span,
      BraidedCategory.braiding_naturality_right_assoc]
  dsimp only [frameCofiberFamilyOperator, frameCofiberSpanOperator]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ihomCurry_pre_whiskerRight,
    Category.assoc, ← ihomCurry_pre_whiskerLeft]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← pre_map]
  simp only [Category.assoc] at ⊢
  rw [he]

/-- 概要：枠の一つの図式の全 span の族。
方針：入力の形状写像を curry する。
規約：Ar[n] がパラメーター。使われ方：入力の零終点の判定。 -/
def frameCofiberSpanFamily {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    arNerve n ⟶ (ihom (horn 2 0 : SSet.{u})).obj C :=
  curry ((β_ (horn 2 0 : SSet.{u}) (arNerve n)).hom ≫ arCofiberSpanMap n ≫ F)

/-- 概要：入力作用素の頂点は個々の枠の span の族。
方針：内部 currying の零次元での計算。
規約：厳密等号。使われ方：全部分複体への持ち上げ。 -/
lemma frameCofiberSpanOperator_vertex {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    (frameCofiberSpanOperator n C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameCofiberSpanFamily F) := rfl

/-- 概要：枠の零対角条件により、各 span の第二辺の終点は零対象。
方針：curry を頂点で評価し、span の第二辺の貼り合わせ式を使う。
規約：quasicategory 性は不要。使われ方：零脚つき span の内部 Hom への持ち上げ。 -/
lemma frameCofiberSpanFamily_zero {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C)
    (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (a : Ar.{u} n) :
    IsZeroSpanVertex ((frameCofiberSpanFamily F).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ a)) := by
  rw [frameCofiberSpanFamily, curry_vertex_value]
  let p : (horn 2 0 : SSet.{u}) ⟶ frameNerve n :=
    CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫ arCofiberSpanMap n
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ p ≫ F))
  have he : horn₂₀.ι₀₂ ≫ p =
      CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫ arCofiberZeroInputMap n := by
    change horn₂₀.ι₀₂ ≫ (CartesianMonoidalCategory.lift _ _ ≫ arCofiberSpanMap n) = _
    have h : horn₂₀.ι₀₂ ≫ CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) =
        CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫
          (arNerve n ◁ horn₂₀.ι₀₂) := by rfl
    rw [← Category.assoc, h, Category.assoc, arCofiberSpanMap_right]
  rw [← Category.assoc, he]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫
    arCofiberZeroInputMap n) ≫ F).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  exact hF (ComposableArrows.mk₀
    (⟨arObj a.down.val.1 a.down.val.1 le_rfl, Or.inr rfl⟩ : FrameAr n)) rfl

/-- 概要：零対角の枠から零脚つき span の全区間の族を取る。
方針：内部 Hom の全部分複体表示へ頂点ごとの零終点条件で持ち上げる。
規約：入力の零射を固定する。使われ方：cofiberSpanProjection の相対内部 Hom。 -/
def frameCofiberSpans (n : ℕ) (C : SSet.{u}) :
    zeroFrameDiagrams n C ⟶ (ihom (arNerve n)).obj (zeroSpanDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n)
      ((ihom (horn 2 0 : SSet.{u})).obj C) IsZeroSpanVertex)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ frameCofiberSpanOperator n C) (by
      intro v
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (frameNerve n) C).symm v.val
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      have hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
        rw [hv]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies _ _ _
        ((frameCofiberSpanOperator n C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv, frameCofiberSpanOperator_vertex]
      intro a
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      have ha : a = ComposableArrows.mk₀ (nerveEquiv a) :=
        (nerveEquiv.symm_apply_apply a).symm
      rw [ha]
      exact frameCofiberSpanFamily_zero F hF (nerveEquiv a)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso (arNerve n)
      ((ihom (horn 2 0 : SSet.{u})).obj C) IsZeroSpanVertex).inv

/-- 概要：零脚の条件を忘れると元の span 入力作用素。
方針：内部 Hom の全部分複体同型と持ち上げの包含後の式を使う。
規約：全次数で厳密等号。使われ方：境界と枠の入力の照合。 -/
lemma frameCofiberSpans_ι (n : ℕ) (C : SSet.{u}) :
    frameCofiberSpans n C ≫
      (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ frameCofiberSpanOperator n C := by
  rw [frameCofiberSpans, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso_inv_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

/-- 概要：gapped 図式の cofiber 族の span は枠の零脚つき入力に一致。
方針：零脚条件を忘れる単射の後で抽出作用素の span の式を使う。
規約：全パラメーターの厳密等号。使われ方：相対持ち上げ問題の境界。 -/
lemma gappedCofiberFamiliesMap_span (n : ℕ) (C : SSet.{u}) :
    gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberSpanProjection C) =
      gappedFrameRestriction n C ≫ frameCofiberSpans n C := by
  apply (cancel_mono ((ihom (arNerve n)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι)).1
  rw [Category.assoc, ← Functor.map_comp, cofiberSpanProjection_ι,
    cofiberSpan, Functor.map_comp, ← Category.assoc, gappedCofiberFamiliesMap_ι,
    Category.assoc, arCofiberFamilyOperator_span, ← Category.assoc,
    ← gappedFrameRestriction_ι, Category.assoc, ← frameCofiberSpans_ι]
  simp only [Category.assoc]

/-- 概要：枠の cofiber 抽出も全 span の入力を厳密に回収する。
方針：包含後で内部 Hom の自然性と span の抽出式を合わせる。
規約：C は quasicategory。使われ方：枠と境界を同時に固定する持ち上げ。 -/
lemma zeroFrameCofiberFamiliesMap_span (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    zeroFrameCofiberFamiliesMap n C ≫
      (ihom (frameNerve n)).map (cofiberSpanProjection C) =
      frameCofiberSpans n C ≫ (pre (frameInclusion n)).app (zeroSpanDiagrams C) := by
  apply (cancel_mono ((ihom (frameNerve n)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι)).1
  rw [Category.assoc, ← Functor.map_comp, cofiberSpanProjection_ι,
    cofiberSpan, Functor.map_comp, ← Category.assoc, zeroFrameCofiberFamiliesMap_ι,
    Category.assoc, frameCofiberFamilyOperator_span]
  rw [Category.assoc, ← (pre (frameInclusion n)).naturality]
  simp only [← Category.assoc]
  rw [frameCofiberSpans_ι]

end SerrePositivity.KST.SConstruction

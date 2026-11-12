module
public import SerrePositivity.KST.ProExcision.TensorAugmentationNaturality
public import SerrePositivity.KST.ProExcision.StrictificationFunctoriality

/-!
# 異なる因子間の augmentation 補正の実比較の自然性

概要：二組の因子内の実ホモトピーを結ぶ射の下で A.5 の実区間比較は自然。
方針：一般の鎖比較の自然性、厳密化の自然性、低次区間復元の自然性を合成する。
規約：KST A.5 の augmentation 補正と Lemma 4.16 の (I,a) の射への関手性。
使われ方：非可換な係数環の変更と単体環の各次数間の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial

/-- 概要：異なる鎖複体を結ぶ三つの正方形の合成は可換。
方針：結合則で三つの正方形を順に使う。
規約：KST A.5。使われ方：低次一致する比較先の前後合成の自然性。 -/
lemma chainComparisonWhisker_square
    {A A' B B' C C' D D' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (a : A ⟶ B) (a' : A' ⟶ B') (r : B ⟶ C) (r' : B' ⟶ C') (b : C ⟶ D) (b' : C' ⟶ D')
    (z : A ⟶ A') (x : B ⟶ B') (y : C ⟶ C') (w : D ⟶ D')
    (ha : z ≫ a' = a ≫ x) (hr : x ≫ r' = r ≫ y) (hb : y ≫ b' = b ≫ w) :
    z ≫ ((a' ≫ r') ≫ b') = ((a ≫ r) ≫ b) ≫ w := by
  calc
    _ = a ≫ (x ≫ r') ≫ b' := by simp only [← Category.assoc, ha]
    _ = a ≫ (r ≫ y) ≫ b' := by rw [hr]
    _ = _ := by simp only [Category.assoc, hb]

/-- 概要：補正したテンソルの実区間比較は異なる二組の入力を結ぶ射に自然。
方針：因子内の入力の自然性から厳密化と鎖比較の自然性を導き、実区間へ復元する。
規約：KST A.5 の augmentation 補正、(I,a) の関手性。次数上限は両組で同じ。
使われ方：群準同型の係数変更と単体環への移送。 -/
lemma linearizedTensorAugmentationMHomotopy_functorial
    {X Y Z U V W X₁ Y₁ Z₁ U₁ V₁ W₁ : SSet.{u}}
    {f e : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U}
    {g e' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V}
    {f₁ e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U₁}
    {g₁ e₁' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V₁} {m m' : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f e m) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g e' m')
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f₁ e₁ m) (k₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g₁ e₁' m')
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace W)
    (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Z₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y₁))
    (b₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V₁) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace W₁)
    (x : X ⟶ X₁) (y : Y ⟶ Y₁) (z : Z ⟶ Z₁) (u : U ⟶ U₁) (v : V ⟶ V₁) (w : W ⟶ W₁)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ f₁ = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ g₁ = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ e₁ = e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (he' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ e₁' = e' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (hh : linearizedCylinderMap x ≫ h₁.h = h.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (hk : linearizedCylinderMap y ≫ k₁.h = k.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z ≫ a₁ =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) ≫ b₁ =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) :
    linearizedCylinderMap z ≫ (linearizedTensorAugmentationMHomotopy h₁ k₁ a₁ b₁).h =
      (linearizedTensorAugmentationMHomotopy h k a b).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w := by
  have hF := strictifiedMap_naturality h h₁ x u hf hh
  have hG := strictifiedMap_naturality k k₁ y v hg hk
  have hnF := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hF
  have hnG := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hG
  have hne := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) he
  have hne' := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) he'
  simp only [CategoryTheory.Functor.map_comp] at hnF hnG hne hne'
  have hnh := normalizedStrictificationHomotopy_square h h₁ x u
    (strictificationHomotopy_naturality h h₁ x u hf hh)
  have hnk := normalizedStrictificationHomotopy_square k k₁ y v
    (strictificationHomotopy_naturality k k₁ y v hg hk)
  have hleft := normalizedTensorComparisonWithHomotopies_square f g f₁ g₁
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    h₁.normalizedStrictificationHomotopy k₁.normalizedStrictificationHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    hf hg hnF hnh hnk
  have hright := normalizedTensorAugmentationComparison_square f e g e' f₁ e₁ g₁ e₁'
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    h₁.normalizedStrictificationHomotopy k₁.normalizedStrictificationHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    hf hg he he' hnF hnh hnk
  have hterm (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V)
      (F₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U₁) (G₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V₁)
      (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ F₁ = F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
      (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ G₁ = G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z ≫ (a₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap F₁ G₁ ≫ b₁) =
        (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap F G ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w := by
    rw [← Category.assoc, ha]
    simp only [Category.assoc]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) _),
      ← simplicialIntegerTensorMap_comp, hF, hG, simplicialIntegerTensorMap_comp]
    simp only [Category.assoc]
    rw [hb]
  have han := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) ha
  have hbn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hb
  simp only [CategoryTheory.Functor.map_comp] at han hbn
  dsimp only [linearizedTensorAugmentationMHomotopy]
  apply linearizedMHomotopyOfChainComparisons_naturality _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w)
  · exact hterm f g f₁ g₁ hf hg
  · simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, Category.assoc]
    rw [hterm f e' f₁ e₁' hf he', hterm e g e₁ g₁ he hg, hterm e e' e₁ e₁' he he']
    simp only [Category.assoc]
  · have ht := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map k.strictifiedMap)
      ((normalizedMooreComplex _).map h₁.strictifiedMap) ((normalizedMooreComplex _).map k₁.strictifiedMap)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hnF hnG
    exact chainComparisonWhisker_square _ _ _ _ _ _ _ _ _ _ han ht hbn
  · have ht₁ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map e')
      ((normalizedMooreComplex _).map h₁.strictifiedMap) ((normalizedMooreComplex _).map e₁')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hnF hne'
    have ht₂ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map k.strictifiedMap)
      ((normalizedMooreComplex _).map e₁) ((normalizedMooreComplex _).map k₁.strictifiedMap)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hne hnG
    have ht₃ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map e')
      ((normalizedMooreComplex _).map e₁) ((normalizedMooreComplex _).map e₁')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hne hne'
    have ht := congrArg₂ (fun r s ↦ r - s) (congrArg₂ (fun r s ↦ r + s) ht₁ ht₂) ht₃
    simp only [← Preadditive.comp_add, ← Preadditive.comp_sub,
      ← Preadditive.add_comp, ← Preadditive.sub_comp] at ht
    apply chainComparisonWhisker_square _ _ _ _ _ _ _ _ _ _ han _ hbn
    simpa only [Preadditive.comp_add, Preadditive.comp_sub,
      Preadditive.add_comp, Preadditive.sub_comp] using ht
  · apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
    exact normalizedComparisonWhisker_square _ _ a a₁ b b₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) ha hb hleft
  · apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
    exact normalizedComparisonWhisker_square _ _ a a₁ b b₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) ha hb hright

end SerrePositivity.KST.ProExcision

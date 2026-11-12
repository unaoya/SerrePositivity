module
public import SerrePositivity.KST.ProExcision.TensorAugmentationMHomotopy
public import SerrePositivity.KST.ProExcision.NormalizedTensorSandwichNaturality
public import SerrePositivity.KST.ProExcision.NormalizedStrictificationNaturality
public import SerrePositivity.KST.ProExcision.LowChainComparisonNaturality

/-!
# augmentation 補正の実区間比較への自然性の移送

概要：二因子の正規化鎖比較から実区間比較までの構成に自然性を渡す。
方針：全鎖比較を前後合成し、二つの低次一致する比較からの復元を使う。
規約：KST Construction A.5 の右辺の augmentation 補正、非被約 C(H) を保つ。
使われ方：同変な入力の厳密化を μ 版 A.5 の同変な実ホモトピーへつなぐ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial

/-- 概要：可換な三つの正方形の合成も可換。
方針：合成の結合則で三つの等式を順に使う。
規約：KST A.5、実鎖比較の前後合成。
使われ方：対角と μ で挟んだ比較先の自然性。 -/
lemma chainComparisonWhisker_naturality
    {A B C D : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (a : A ⟶ B) (r : B ⟶ C) (b : C ⟶ D)
    (z : A ⟶ A) (x : B ⟶ B) (y : C ⟶ C) (w : D ⟶ D)
    (ha : z ≫ a = a ≫ x) (hr : x ≫ r = r ≫ y) (hb : y ≫ b = b ≫ w) :
    z ≫ ((a ≫ r) ≫ b) = ((a ≫ r) ≫ b) ≫ w := by
  calc
    _ = a ≫ (x ≫ r) ≫ b := by simp only [← Category.assoc, ha]
    _ = a ≫ (r ≫ y) ≫ b := by rw [hr]
    _ = _ := by simp only [Category.assoc, hb]

/-- 概要：自然な鎖比較の前後合成も自然。
方針：正規化の関手性と鎖ホモトピーの前後合成の自然性を使う。
規約：KST A.5、対角と μ の前後合成の共通部分。
使われ方：実区間復元に入力する二つの鎖比較の自然性。 -/
lemma normalizedComparisonWhisker_square
    {C C' D D' E E' F F' : SimplicialObject (ModuleCat.{u} ℤ)}
    {f : C ⟶ D} {f' : C' ⟶ D'}
    {R : (normalizedMooreComplex _).obj C ⟶ (normalizedMooreComplex _).obj D}
    {R' : (normalizedMooreComplex _).obj C' ⟶ (normalizedMooreComplex _).obj D'}
    (H : Homotopy ((normalizedMooreComplex _).map f) R)
    (H' : Homotopy ((normalizedMooreComplex _).map f') R')
    (a : E ⟶ C) (a' : E' ⟶ C') (b : D ⟶ F) (b' : D' ⟶ F')
    (x : C ⟶ C') (y : D ⟶ D') (z : E ⟶ E') (w : F ⟶ F')
    (ha : z ≫ a' = a ≫ x) (hb : y ≫ b' = b ≫ w)
    (hH : ChainHomotopySquare ((normalizedMooreComplex _).map x)
      ((normalizedMooreComplex _).map y) H H') :
    ChainHomotopySquare ((normalizedMooreComplex _).map z) ((normalizedMooreComplex _).map w)
      ((H.compLeft ((normalizedMooreComplex _).map a)).compRight ((normalizedMooreComplex _).map b))
      ((H'.compLeft ((normalizedMooreComplex _).map a')).compRight ((normalizedMooreComplex _).map b')) := by
  apply ChainHomotopySquare.compRight
  · apply ChainHomotopySquare.compLeft hH
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) ha
  · simpa only [CategoryTheory.Functor.map_comp] using
      congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hb

/-- 概要：補正したテンソルの実区間比較は入力の自然な正方形を保つ。
方針：二つの全鎖比較の自然性を前後合成し、低次の区間復元へ渡す。
規約：KST A.5 の augmentation 補正、入力の全比較は因子内に値を持つ。
使われ方：μ 版の外部 G 同変性を作用の各自己射について導く。 -/
lemma linearizedTensorAugmentationMHomotopy_naturality
    {X Y Z U V W : SSet.{u}}
    {f e : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U}
    {g e' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V} {m m' : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f e m) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g e' m')
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace W)
    (x : X ⟶ X) (y : Y ⟶ Y) (z : Z ⟶ Z) (u : U ⟶ U) (v : V ⟶ V) (w : W ⟶ W)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ g = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ e = e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (he' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ e' = e' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ h.strictifiedMap = h.strictifiedMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ k.strictifiedMap = k.strictifiedMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ h.strictificationHomotopy.h =
        h.strictificationHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
    (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ k.strictificationHomotopy.h =
        k.strictificationHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z ≫ a =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) ≫ b =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ (linearizedTensorAugmentationMHomotopy h k a b).h =
        (linearizedTensorAugmentationMHomotopy h k a b).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w := by
  have hnF := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hF
  have hnG := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hG
  have hne := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) he
  have hne' := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) he'
  simp only [CategoryTheory.Functor.map_comp] at hnF hnG hne hne'
  have hnh := normalizedStrictificationHomotopy_square h h x u hh
  have hnk := normalizedStrictificationHomotopy_square k k y v hk
  have hleft := normalizedTensorComparisonWithHomotopies_square f g f g
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    hf hg hnF hnh hnk
  have hright := normalizedTensorAugmentationComparison_square f e g e' f e g e'
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    h.normalizedStrictificationHomotopy k.normalizedStrictificationHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v)
    hf hg he he' hnF hnh hnk
  dsimp only [linearizedTensorAugmentationMHomotopy]
  apply linearizedMHomotopyOfChainComparisons_naturality _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w)
  · rw [← Category.assoc, ha]
    simp only [Category.assoc]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) _),
      ← simplicialIntegerTensorMap_comp, hf, hg, simplicialIntegerTensorMap_comp]
    simp only [Category.assoc]
    rw [hb]
  · simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp, Preadditive.sub_comp]
    have hterm (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace U)
        (G : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace V)
        (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ F = F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u)
        (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y ≫ G = G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z ≫ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap F G ≫ b) =
          (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap F G ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w := by
      rw [← Category.assoc, ha]
      simp only [Category.assoc]
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) _),
        ← simplicialIntegerTensorMap_comp, hF, hG, simplicialIntegerTensorMap_comp]
      simp only [Category.assoc]
      rw [hb]
    simp only [Category.assoc]
    rw [hterm f e' hf he', hterm e g he hg, hterm e e' he he']
    simp only [Category.assoc]
  · have ht := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map k.strictifiedMap)
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map k.strictifiedMap)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hnF hnG
    have han := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) ha
    have hbn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hb
    simp only [CategoryTheory.Functor.map_comp] at han hbn
    exact chainComparisonWhisker_naturality _ _ _ _ _ _ _ han ht hbn
  · have ht₁ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map e')
      ((normalizedMooreComplex _).map h.strictifiedMap) ((normalizedMooreComplex _).map e')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hnF hne'
    have ht₂ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map k.strictifiedMap)
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map k.strictifiedMap)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hne hnG
    have ht₃ := normalizedTensorSandwich_naturality
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map e')
      ((normalizedMooreComplex _).map e) ((normalizedMooreComplex _).map e')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v) hne hne'
    have han := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) ha
    have hbn := congrArg ((normalizedMooreComplex (ModuleCat.{u} ℤ)).map) hb
    simp only [CategoryTheory.Functor.map_comp] at han hbn
    have ht := (congrArg₂ (fun r s ↦ r - s) (congrArg₂ (fun r s ↦ r + s) ht₁ ht₂) ht₃)
    simp only [← Preadditive.comp_add, ← Preadditive.comp_sub,
      ← Preadditive.add_comp, ← Preadditive.sub_comp] at ht
    apply chainComparisonWhisker_naturality _ _ _ _ _ _ _ han _ hbn
    simpa only [Preadditive.comp_add, Preadditive.comp_sub,
      Preadditive.add_comp, Preadditive.sub_comp] using ht
  · apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
    exact normalizedComparisonWhisker_square _ _ a a b b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) ha hb hleft
  · apply ChainHomotopySquare.trans (ChainHomotopySquare.ofEq _ _ _ _)
    exact normalizedComparisonWhisker_square _ _ a a b b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap u) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap w) ha hb hright

end SerrePositivity.KST.ProExcision

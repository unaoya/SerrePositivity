module
public import SerrePositivity.KST.ProExcision.TensorHomotopyComponents

/-!
# 恒等へ至る二つのホモトピーのテンソルの自然性

概要：入力の写像に自然な二つの収縮は全テンソルへ移しても自然。
方針：標準包含上の水平・垂直成分で二つの自然性の正方形を比較する。
規約：KST Construction A.5、自然性の入力は実ホモトピーの成分の等式。
使われ方：Moore 収縮のテンソルの外部群同変性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：恒等へ至る二つの自然な収縮の全テンソルも成分ごとに自然。
方針：各二重次数で二つのテンソル成分の合成則を使う。
規約：KST A.5、構成済みのホモトピーの成分の自然性を使う一般の移送補題。
使われ方：実 Moore 収縮をこの補題へ適用する。 -/
lemma chainIntegerTensorHomotopyToId_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f : K ⟶ K} {f' : K' ⟶ K'} {g : L ⟶ L} {g' : L' ⟶ L'}
    (h : Homotopy f (𝟙 K)) (h' : Homotopy f' (𝟙 K'))
    (k : Homotopy g (𝟙 L)) (k' : Homotopy g' (𝟙 L'))
    (a : K ⟶ K') (b : L ⟶ L') (hg : b ≫ g' = g ≫ b)
    (hh : ∀ i, a.f i ≫ h'.hom i (i + 1) = h.hom i (i + 1) ≫ a.f (i + 1))
    (hk : ∀ i, b.f i ≫ k'.hom i (i + 1) = k.hom i (i + 1) ≫ b.f (i + 1)) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap a b).f n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy h' k').hom n (n + 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy h k).hom n (n + 1) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap a b).f (n + 1) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap, Category.assoc,
    ι_chainIntegerTensorHomotopy]
  rw [← Category.assoc (ιMapBifunctor K L _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n hpq),
    ι_chainIntegerTensorHomotopy]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap]
  have hgb := congrArg (fun t ↦ t.f q) hg
  change b.f q ≫ g'.f q = g.f q ≫ b.f q at hgb
  congr 1
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, hh p, hgb,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, Category.assoc]
  · congr 1
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (a.f p ≫ 𝟙 _) (b.f q ≫ k'.hom q (q + 1)) ≫ _ = _
    rw [Category.comp_id, hk q]
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, HomologicalComplex.id_f, Category.id_comp]

end SerrePositivity.KST.ProExcision

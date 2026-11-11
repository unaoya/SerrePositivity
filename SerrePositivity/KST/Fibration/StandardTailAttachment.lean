module
public import SerrePositivity.KST.Fibration.TailAttachment

/-! # 先行標準単体と最後の標準辺の元の貼り合わせ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の先行錐を先行標準単体へ戻す同型。 -/
def tailPrefixStdIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) (Λ[1, 0] : SSet.{u}) ≅ Δ[n + 1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor (Δ[n] : SSet.{u})).mapIso initialHornPointIso.symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0

/-- 元の先行標準単体を貼り合わせに含める。 -/
def standardTailPrefix (n : ℕ) :
    (Δ[n + 1] : SSet.{u}) ⟶ (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) :=
  (tailPrefixStdIso n).inv ≫ tailAttachmentPrefix Δ[n]

/-- 共有端点は元の先行錐の右頂点を標準単体に戻したもの。 -/
def standardTailEndpoint (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  initialHornPointIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] (Λ[1, 0] : SSet.{u}) ≫ (tailPrefixStdIso n).hom

/-- 元の零単体の共有端点に沿って、先行標準単体と最後の辺を貼り合わせる普遍性。 -/
theorem standardTail_isPushout (n : ℕ) :
    IsPushout (stdSimplex.δ (1 : Fin 2)) (standardTailEndpoint n)
      (tailAttachmentEdge (Δ[n] : SSet.{u})) (standardTailPrefix n) := by
  apply (tailAttachment_isPushout (Δ[n] : SSet.{u})).of_iso initialHornPointIso.symm
    (Iso.refl _) (tailPrefixStdIso n) (Iso.refl _)
  · rw [Iso.refl_hom, Category.comp_id, ← initialHornPointIso_ι,
      Iso.symm_hom, Iso.inv_hom_id_assoc]
  · change _ ≫ _ = initialHornPointIso.inv ≫ (initialHornPointIso.hom ≫ _ ≫ _)
    rw [Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change _ ≫ 𝟙 _ = _ ≫ ((tailPrefixStdIso n).inv ≫ _)
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]

/-- 貼り合わせから元の長い標準単体への包含。 -/
def standardTailInclusion (n : ℕ) :
    (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) ⟶ Δ[n + 2] :=
  (tailAttachment (Δ[n] : SSet.{u})).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom

/-- この元の標準単体への包含は inner anodyne。 -/
lemma standardTailInclusion_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (standardTailInclusion.{u} n) := by
  exact innerAnodyneExtensions.comp_mem _ _ (tailAttachment_innerAnodyne Δ[n])
    (innerAnodyneExtensions.of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom)

/-- 元の長い標準単体上の全図式から貼り合わせへの制限は全境界持ち上げを持つ。 -/
lemma standardTailInclusion_pre_trivialKanFibration (n : ℕ) (B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((MonoidalClosed.pre (standardTailInclusion n)).app B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _ (standardTailInclusion_innerAnodyne n) B

end SerrePositivity.KST.Fibration

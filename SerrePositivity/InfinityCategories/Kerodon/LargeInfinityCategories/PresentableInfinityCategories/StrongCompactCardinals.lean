module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ImageCompactGenerators
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactEquivalence

/-!
概要：二つの accessible 関手について、compact 対象の像も compact となる共通濃度を構成する。
方針：両始域を元の Ind 模型へ移し、小さい二つの生成族の像に共通濃度を選ぶ。
規約：固定頂点写像の小ささは具体的な Ind 模型だけに使い、元の圏への追加条件にしない。
使われ方：引き戻しの両成分の filtered 表示と標的像を同じ濃度へ揃える。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の Ind 比較に沿って compact 対象の像の保存を戻す。
方針：逆同値で対象を戻し、同じ関手全同型の成分で像を比較する。
規約：元の対象と全関手 G を保持する。
使われ方：strict 模型上での compact 保存から一般の accessible 圏への輸送。 -/
lemma compactImages_of_equivalence {μ : Cardinal.{u}} {M C D : SSet.{u + 1}}
    [Quasicategory M] [Quasicategory C] [Quasicategory D]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence M C) (G : C ⟶ D)
    (h : ∀ x : M _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((e.hom ≫ G).app _ x)) :
    ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ x) := by
  intro x hx
  have hy := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_iff_equivalence e.symm x).mp hx
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso ((e.invHomIso.postcomp G).app x)).mp
    (h (e.inv.app _ x) hy)

/-- 概要：二つの κ-accessible 関手は、同じ大きい正則 μ に関して全 μ-compact 対象の像を保つ。
方針：二つの小さい Ind 生成族の像を一つの小さい族にまとめ、濃度変更と retract を使う。
規約：始域の厳密な写像の小ささは仮定せず、元の圏の μ-accessibility も同時に供給する。
使われ方：引き戻しの二つの表示の同時濃度調整。 -/
lemma exists_common_compactPreservingCardinal
    {κ : Cardinal.{u}} {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    (p : E ⟶ B) (q : D ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ q)
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D ∧
      (∀ x : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x)) ∧
      (∀ y : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y)) := by
  have : Fact κ.IsRegular := ⟨hE.1⟩
  obtain ⟨AE, hAE, ⟨eE⟩⟩ := hE.exists_indEquivalence
  obtain ⟨AD, hAD, ⟨eD⟩⟩ := hD.exists_indEquivalence
  have := hAE
  have := hAD
  let gE := eE.hom ≫ p
  let gD := eD.hom ≫ q
  let iE := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AE
  let iD := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AD
  let v : AE _⦋0⦌ ⊕ AD _⦋0⦌ → B _⦋0⦌ := Sum.elim
    (fun a ↦ gE.app _ (iE.app _ (ULift.up a)))
    (fun a ↦ gD.app _ (iD.app _ (ULift.up a)))
  obtain ⟨ρ, _, hσρ, himage⟩ := hB.exists_common_compactCardinal v σ
  obtain ⟨μ, hμ, hρμ, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound κ ρ
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hgE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gE :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eE.isQCatEquivalence).comp hp
  have hgD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gD :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eD.isQCatEquivalence).comp hq
  obtain ⟨_, _, _, _, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AE) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AE)
    iE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AE) gE hgE
    (fun a ↦ (himage (Sum.inl a)).of_le hρμ.le)
  obtain ⟨_, _, _, _, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AD) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AD)
    iD (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AD) gD hgD
    (fun a ↦ (himage (Sum.inr a)).of_le hρμ.le)
  exact ⟨μ, hμ, hσρ.trans hρμ, hb, hE.of_cardinalChangeBound hb,
    hD.of_cardinalChangeBound hb, compactImages_of_equivalence eE p he,
    compactImages_of_equivalence eD q hd⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

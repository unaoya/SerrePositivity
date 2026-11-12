module

public import SerrePositivity.KST.LocalizingInvariants.TwoEndpointPullbackFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierNormalizedBoundaryCocone

/-!
概要：元の実分数円柱の両端余錐を、一つの全余錐円柱へ厳密に貼る。
方針：同じ区間境界に前段と次辺の両端を載せ、相対 attachment の実 RLP を適用する。
規約：両端・全前段・全次辺・固定頂点を同じ延長で保持する。
使われ方：一様な完成族側の実余錐と正規化した元の境界余錐の相対接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma pullbackSourcePrefixFamily_pre {S P X : SSet.{u}} {n : ℕ} (j : S ⟶ P)
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily (j ≫ F) = j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily, Category.assoc]

/-- 同じ実次辺円柱を、両端余錐・前段・固定頂点を厳密に保持する一つの全円柱へ貼る。 -/
lemma exists_twoEndpoint_verdierSpanCoconeFamily
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌)
    {S : SSet.{u}} {n : ℕ} (g : S ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x z)
    (F : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g))
    (C₀ C₁ : S ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (h₀p : C₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F)
    (h₁p : C₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F)
    (h₀n : C₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj)
    (h₁n : C₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj) :
    ∃ C : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj,
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ C = C₀ ∧
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ C = C₁ ∧
      C ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F ∧
      C ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj ∧
      C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram C₀ C₁
  have ha : spanIntervalBoundaryMap S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F =
      a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj := by
    dsimp only [a]
    rw [spanIntervalBoundaryDiagram_post]
    exact (spanIntervalBoundaryDiagram_of_endpoints (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F) _ _ h₀p h₁p).symm
  have hb : spanIntervalBoundaryMap S ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj := by
    dsimp only [a]
    rw [spanIntervalBoundaryDiagram_post]
    exact (spanIntervalBoundaryDiagram_of_endpoints
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj)
      _ _ h₀n h₁n).symm
  obtain ⟨C, hj, hp, hn, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_relative_verdierSpanCoconeFamily i x z
    (spanIntervalBoundaryMap S) g F hF a ha hb
  have h₀ := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 S ≫ f) hj
  have h₁ := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 S ≫ f) hj
  rw [← Category.assoc, spanIntervalBoundaryMap_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] at h₀
  rw [← Category.assoc, spanIntervalBoundaryMap_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] at h₁
  exact ⟨C, h₀, h₁, hp, hn, hz⟩

/-- 両端 pullback と両端余錐を同じ区間境界に載せ、二つの実相対充填を接続する。 -/
lemma exists_twoEndpoint_verdierPullbackCoconeFamily
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌)
    {S : SSet.{u}} {n : ℕ} (g : S ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x z)
    (G : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hG : G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g))
    (F₀ F₁ : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (h₀p : F₀ ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj))
    (h₁p : F₁ ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj))
    (h₀t : F₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj))
    (h₁t : F₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ G ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj))
    (C₀ C₁ : S ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (h₀c : C₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F₀)
    (h₁c : C₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F₁)
    (h₀n : C₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj)
    (h₁n : C₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj) :
    ∃ (F : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
      (C : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ F = F₀ ∧
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ F = F₁ ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        G ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) ∧
      F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) ∧
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ C = C₀ ∧
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ C = C₁ ∧
      C ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F ∧
      C ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj ∧
      C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨F, hf₀, hf₁, hFp, hFt⟩ := exists_twoEndpoint_terminalPullbackFamily n G F₀ F₁
    h₀p h₁p h₀t h₁t
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackFamily_evaluate_of_restriction F G hFt).trans hG
  have hc₀ : C₀ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F := by
    rw [← pullbackSourcePrefixFamily_pre, hf₀]
    exact h₀c
  have hc₁ : C₁ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily F := by
    rw [← pullbackSourcePrefixFamily_pre, hf₁]
    exact h₁c
  obtain ⟨C, hc₀, hc₁, hCp, hCn, hCz⟩ := exists_twoEndpoint_verdierSpanCoconeFamily i x z
    g F hF C₀ C₁ hc₀ hc₁ h₀n h₁n
  exact ⟨F, C, hf₀, hf₁, hFp, hFt, hc₀, hc₁, hCp, hCn, hCz⟩

end SerrePositivity.KST.LocalizingInvariants

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKernelResolutionMoritaInfinity
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Coherence
/-!
概要：一般双加群の明示 Morita 三条件と両側 compact 生成から、同じ実 ∞ 関手の同値を得る。
方針：元の実主導来比較自然同型と compact 性の輸送を使う。
規約：生の出力の射影性や局所 Hom 平坦性を追加しない。使われ方：β5 e。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z z'
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ主導来作用による実 kernel の比較。 -/
lemma dgKernelDerivedInfinity_isQCatEquivalence_of_morita
    (P : Bimodule R E D)
    (hP : Morita.CriterionPerfConditions R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)))
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory R D)
    (hG : Morita.CriterionDerivedCompactGeneration R D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory R E)
    (hH : Morita.CriterionDerivedCompactGeneration R E H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  have : (Morita.kernelDerivedTensor R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P))).IsEquivalence :=
    (Morita.kernelMoritaEquivalence R D E _ hP G hG H hH).isEquivalence_functor
  have : (Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_isQCatEquivalence_of_classical R D E P
end SerrePositivity.InfinityCategories.Project.DerivedCategories

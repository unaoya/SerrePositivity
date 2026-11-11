module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelBimoduleIso
/-!
概要：元の双加群同型の導来作用と同じ raw factor の可換四角形を証明する。
方針：元の指定値と同じ実変形円柱を保って照合する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 比較 ξ の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- 元の半自由出力分解へ送った同型は、同じ raw factor と可換。 -/
lemma dgModuleResolvedInfinity_isoOfRawFunctorIso_square
    (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
    (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R C E F G e ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E G =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F ≪≫
        e.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の双加群同型の通常作用を、同じ半自由入力へ制限する。 -/
def dgKernelBimoduleIsoSemifreeNerve {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! h
/-- 元の双加群同型の導来作用は、同じ raw factor と可換。 -/
lemma dgKernelDerivedInfinity_bimoduleIso_rawFactor_square
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)) ≪≫
      (dgKernelBimoduleIsoSemifreeNerve R D E e).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))) := by
  exact dgModuleResolvedInfinity_isoOfRawFunctorIso_square R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))
    (dgKernelBimoduleIsoSemifreeNerve R D E e)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories

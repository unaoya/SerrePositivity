module

public import SerrePositivity.KST.Spectra.D3StageDiagramCorners

/-!
概要：厳密終点を保つ既存 loop 全図式比較の、指定同型に関する自然性を実証する。
方針：同じ終点同型の充満忠実な逆像を使い、指定値の回収則で正方形を反映する。
規約：段の比較同型を選び直さない。標的の指定同型そのものを持ち上げる。
使われ方：実 loop 構造同型と標準図式比較の段間整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 同じ指定同型の端点輸送は、指定された等式同型の正方形を厳密に満たす。 -/
lemma d3FunctorIsoOfEq_triangle {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') :
    eqToIso (congrArg (fun a : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) hf) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg =
    e ≪≫ eqToIso (congrArg
      (fun a : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) hg) := by
  subst f' g'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

variable {A X : SSet.{u}}
  (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)

/-- 元の実全図式族と同じ終点を持つ、指定切断の標準図式族。 -/
def d3LoopCanonicalFamily (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X :=
  (F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) ≫ s

include hs in
lemma d3LoopCanonicalFamily_target (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) :
    d3LoopCanonicalFamily s F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 =
      F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 := by
  rw [d3LoopCanonicalFamily, Category.assoc, hs, Category.comp_id]

variable [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]

/-- 元の厳密終点の同じ実 fiber 内で選ばれる、既存型の全図式比較。 -/
def d3LoopCanonicalDiagramIso (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (d3LoopCanonicalFamily s F) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramFamilyIso_of_section s hs F (d3LoopCanonicalFamily s F)
    (d3LoopCanonicalFamily_target s hs F).symm

lemma d3LoopCanonicalDiagramIso_target (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) :
    (d3LoopCanonicalDiagramIso s hs F).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) =
      eqToIso (congrArg
        (fun a : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
          (d3LoopCanonicalFamily_target s hs F).symm) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoOfTrivialKanFibration_postcomp _ F (d3LoopCanonicalFamily s F)
    (d3LoopCanonicalFamily_target s hs F).symm

/-- 元の終点同型を指定値として持ち上げた、標準全図式族間の同型。 -/
def d3LoopCanonicalTransport {F G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3LoopCanonicalFamily s F) (d3LoopCanonicalFamily s G) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)).preimageFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1))
      (d3LoopCanonicalFamily_target s hs F).symm
      (d3LoopCanonicalFamily_target s hs G).symm)

lemma d3LoopCanonicalTransport_target {F G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    (d3LoopCanonicalTransport s hs e).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1))
        (d3LoopCanonicalFamily_target s hs F).symm
        (d3LoopCanonicalFamily_target s hs G).symm := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  let hf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)
  exact hf.preimageFunctorIso_postcomp _

/-- 既存の実 fiber 比較は、元の指定全図式同型と指定終点の持ち上げに厳密に自然。 -/
lemma d3LoopCanonicalDiagramIso_naturality {F G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    d3LoopCanonicalDiagramIso s hs F ≪≫ d3LoopCanonicalTransport s hs e =
      e ≪≫ d3LoopCanonicalDiagramIso s hs G := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  let hf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)
  apply hf.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    d3LoopCanonicalDiagramIso_target, d3LoopCanonicalDiagramIso_target,
    d3LoopCanonicalTransport_target]
  exact d3FunctorIsoOfEq_triangle _ _ _

end SerrePositivity.KST.Spectra

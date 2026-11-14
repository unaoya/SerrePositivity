module

public import SerrePositivity.KST.Spectra.D3StageReflectionStructure

/-!
概要：保持した模型間比較を、元の始域四角形全体の転置へ移す。
方針：厳密終点を保つ指定転置同型の逆と、同じ既存比較を合成する。
規約：始点反転を自由に挿入しない。模型補正の消滅や B の完成は主張しない。
使われ方：反転を含む正しい模型比較の候補を、全図式と指定始点の両方で保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

private lemma d3ReflectedIso_normalize_symm {A X : SSet.{u}}
    {f g f' g' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e.symm hg hf = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).symm := by
  subst f' g'
  rfl

private lemma d3ReflectedIso_normalize_trans {A X : SSet.{u}}
    {f g h f' g' h' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h)
    (hf : f = f') (hg : g = g') (hh : h = h') :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ d) hf hh =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d hg hh := by
  subst f' g' h'
  rfl

section
variable {A X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
  (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
  (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)

/-- 同じ全パラメータ図式を転置へ送る、終点固定の指定比較。 -/
def d3LoopFamilyTransposeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (F ≫ d3LoopDiagramTranspose X) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3LoopDiagramTransposeIso s hs).precomp F) (Category.comp_id F) rfl

lemma d3LoopFamilyTransposeIso_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso ((d3LoopFamilyTransposeIso s hs F).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)) := by
  have h := (d3LoopDiagramTransposeIso_target_isEq s hs).precomp F
  apply h.of_heq (by simp only [Category.id_comp]) rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp _ _ _))

/-- 指定転置比較の始点は、同じ全図式反転の前合成そのもの。 -/
lemma d3LoopFamilyTransposeIso_source :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3LoopFamilyTransposeIso s hs F).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) rfl
      (by rw [Category.assoc, d3LoopDiagramTranspose_corner]) =
    (d3LoopDiagramReflection s hs).precomp F := by
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq
    ((d3LoopDiagramTransposeIso s hs).precomp F) (Category.comp_id F) rfl
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp (d3LoopDiagramTransposeIso s hs) F
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq
    ((d3LoopDiagramTransposeIso s hs).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (Category.id_comp _) (d3LoopDiagramTranspose_corner X 0 0) F
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    (h0.trans ((heq_of_eq h1).trans h2.symm)))

/-- 同じ比較射を、始域の実四角形全体を転置して保持する。 -/
def d3LoopReflectedFamilyComparison {G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ d3LoopDiagramTranspose X) G :=
  (d3LoopFamilyTransposeIso s hs F).symm ≪≫ e

/-- 転置した比較から元の指定全図式比較を厳密回収する。 -/
lemma d3LoopReflectedFamilyComparison_recover {G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    d3LoopFamilyTransposeIso s hs F ≪≫ d3LoopReflectedFamilyComparison s hs F e = e := by
  simp only [d3LoopReflectedFamilyComparison, ← Iso.trans_assoc,
    Iso.self_symm_id, Iso.refl_trans]

/-- 転置後も終点成分は、元の終点固定の比較のまま。 -/
lemma d3LoopReflectedFamilyComparison_target {G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso ((d3LoopReflectedFamilyComparison s hs F e).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)) := by
  rw [d3LoopReflectedFamilyComparison, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm]
  exact (d3LoopFamilyTransposeIso_target s hs F).symm.trans he

/-- 反転は始点だけの選択でなく、同じ転置済み全図式比較から回収される。 -/
lemma d3LoopReflectedFamilyComparison_source {G : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3LoopReflectedFamilyComparison s hs F e).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
      (by rw [Category.assoc, d3LoopDiagramTranspose_corner]) rfl =
    ((d3LoopDiagramReflection s hs).precomp F).symm ≪≫
      e.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) := by
  rw [d3LoopReflectedFamilyComparison, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, d3ReflectedIso_normalize_trans _ _ _ rfl,
    d3ReflectedIso_normalize_symm, d3LoopFamilyTransposeIso_source]
  rfl
end

namespace OmegaSpectrum.AdjointLoopRelativeBF

/-- 保持した実模型比較の始域を全四角形として転置した候補。 -/
def commonChosenStageLoopReflectedComparison (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageLoopedCanonicalFamily.{u} n ≫
      d3LoopDiagramTranspose PointedKanInfinity) (commonChosenStageCanonicalImageFamily n) :=
  d3LoopReflectedFamilyComparison d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageLoopedCanonicalFamily n) (commonChosenStageLoopImageComparison n)

/-- 転置後の実全図式も、元の実次段 loop 像と同じ厳密終点を持つ。 -/
lemma commonChosenStageLoopReflectedComparison_target_eq (n : ℕ) :
    (commonChosenStageLoopedCanonicalFamily.{u} n ≫
      d3LoopDiagramTranspose PointedKanInfinity) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
    commonChosenStageLoopImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 := by
  rw [Category.assoc, d3LoopDiagramTranspose_corner]
  exact commonChosenStageLoopedCanonicalFamily_target n

/-- 元の保持済み模型比較を、転置前後の指定全図式比較から回収する。 -/
lemma commonChosenStageLoopReflectedComparison_recover (n : ℕ) :
    d3LoopFamilyTransposeIso d3PointedKanLoopSection d3PointedKanLoopSection_target
      (commonChosenStageLoopedCanonicalFamily.{u} n) ≪≫
        commonChosenStageLoopReflectedComparison n = commonChosenStageLoopImageComparison n :=
  d3LoopReflectedFamilyComparison_recover d3PointedKanLoopSection
    d3PointedKanLoopSection_target (commonChosenStageLoopedCanonicalFamily n)
    (commonChosenStageLoopImageComparison n)

lemma commonChosenStageLoopReflectedComparison_target (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso ((commonChosenStageLoopReflectedComparison.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  apply d3LoopReflectedFamilyComparison_target
  exact d3IsFunctorEqIso_of_eqToIso _ (commonChosenStageLoopImageComparison_target_eq n)
    (commonChosenStageLoopImageComparison_target n)

/-- 実模型比較の転置は、始点では同じ全図式反転の逆を正確に挿入する。 -/
lemma commonChosenStageLoopReflectedComparison_source (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonChosenStageLoopReflectedComparison.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
      (by rw [Category.assoc, d3LoopDiagramTranspose_corner]) rfl =
    ((d3LoopDiagramReflection d3PointedKanLoopSection
      d3PointedKanLoopSection_target).precomp (commonChosenStageLoopedCanonicalFamily n)).symm ≪≫
      (commonChosenStageLoopImageComparison n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3LoopReflectedFamilyComparison_source d3PointedKanLoopSection
    d3PointedKanLoopSection_target (commonChosenStageLoopedCanonicalFamily n)
    (commonChosenStageLoopImageComparison n)

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra

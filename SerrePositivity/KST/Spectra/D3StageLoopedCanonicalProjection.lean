module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

public import SerrePositivity.KST.Spectra.D3StageLoopedCanonical

/-!
概要：既存の次段比較の loop 像を、同じ指定射影値・各角の値まで保持する。
方針：後合成と評価の厳密交換、充満忠実な逆像の指定値保持、等式同型の保存を使う。
規約：元の次段比較を自由な同型で置き換えない。円交換因子を比較しない。
使われ方：loop 像の比較を、次段像側の標準図式比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 元の厳密等式の同型は、同じ指定値を持つ等式由来の同型である。 -/
lemma d3IsFunctorEqIso_of_eqToIso {A X : SSet.{u}} {f g : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (h : f = g)
    (he : e = eqToIso (congrArg
      (fun a : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) h)) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e := by
  subst g
  subst e
  exact ⟨rfl, rfl⟩

/-- 等式由来の同じ指定値は、任意の同じ端点等式の同型として回収できる。 -/
lemma d3IsFunctorEqIso_eqToIso {A X : SSet.{u}} {f g : A ⟶ X}
    {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e) (h : f = g) :
    e = eqToIso (congrArg
      (fun a : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) h) := by
  rcases he with ⟨h', he⟩
  subst g
  subst e
  rfl

namespace OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ次段比較の loop 像の四角形を評価すると、元の比較の同じ角の loop を回収する。 -/
lemma commonChosenStageLoopedCanonicalSquareIso_corner (n : ℕ) (i j : Fin 2) :
    HEq ((commonChosenStageLoopedCanonicalSquareIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := PointedKanInfinity)
        (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      ((commonChosenStageCanonicalDiagramIso (n + 1)).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j ≫ pointedKanLoopInfinity)) := by
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity
  let ev := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]))
    (Y := PointedKanInfinity) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)
  have hm : p ≫ ev = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j ≫ pointedKanLoopInfinity := by
    dsimp only [p, ev, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
    rw [Category.assoc, d3SquareEvaluation_postcomp, ← Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq
    ((commonChosenStageCanonicalDiagramIso (n + 1)).postcomp p)
    (show _ = commonChosenStageLoopImageSquareFamily n from by
      simp only [p, commonChosenStageLoopImageSquareFamily,
        ← commonChosenStageLoopDiagramFamily_ι, Category.assoc])
    (show _ = commonChosenStageLoopedCanonicalSquareFamily n from by
      simp only [p, commonChosenStageLoopedCanonicalSquareFamily, Category.assoc]) ev
  exact h.trans ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp _ p ev)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq _ hm))

/-- 回収した実 loop 全図式の loop 像同型は、元の指定全四角形同型へ戻る。 -/
lemma commonChosenStageLoopedCanonicalDiagramIso_projection (n : ℕ) :
    HEq ((commonChosenStageLoopedCanonicalDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι)
        (commonChosenStageLoopedCanonicalSquareIso n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        (commonChosenStageLoopImageFamily n) (commonChosenStageLoopedCanonicalFamily n)
        (commonChosenStageLoopedCanonicalSquareIso n)
        (commonChosenStageLoopImageFamily_ι n).symm
        (commonChosenStageLoopedCanonicalFamily_ι n).symm

/-- 同じ loop 像の実全図式同型も、各角で元の次段比較の同じ後合成を回収する。 -/
lemma commonChosenStageLoopedCanonicalDiagramIso_corner (n : ℕ) (i j : Fin 2) :
    HEq ((commonChosenStageLoopedCanonicalDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      ((commonChosenStageCanonicalDiagramIso (n + 1)).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j ≫ pointedKanLoopInfinity)) := by
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
  let ev := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]))
    (Y := PointedKanInfinity) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (commonChosenStageLoopedCanonicalSquareIso n)
    ((commonChosenStageLoopedCanonicalDiagramIso n).postcomp ι)
    (commonChosenStageLoopImageFamily_ι n).symm
    (commonChosenStageLoopedCanonicalFamily_ι n).symm
    (commonChosenStageLoopedCanonicalDiagramIso_projection n) ev
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp (commonChosenStageLoopedCanonicalDiagramIso n) ι ev
  exact (heq_of_eq hc.symm).trans
    (h.trans (commonChosenStageLoopedCanonicalSquareIso_corner n i j))

/-- 同じ loop 像の実図式比較は、終点射影で元の厳密等式の指定値を保つ。 -/
lemma commonChosenStageLoopedCanonicalDiagramIso_target_isEq (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso ((commonChosenStageLoopedCanonicalDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  have h0 := d3IsFunctorEqIso_of_eqToIso _
    (commonChosenStageCanonicalFamily_target (n + 1)).symm
    (commonChosenStageCanonicalDiagramIso_target (n + 1))
  have h1 := h0.postcomp pointedKanLoopInfinity
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp] at h1
  apply h1.of_heq
    (show commonChosenStageLoopDiagramFamily (n + 1) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 ≫ pointedKanLoopInfinity) = _ from by
      rw [← Category.assoc, commonChosenStageLoopImageFamily_corner])
    (show commonChosenStageCanonicalFamily (n + 1) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 ≫ pointedKanLoopInfinity) = _ from by
      rw [← Category.assoc, commonChosenStageLoopedCanonicalFamily_corner])
  exact commonChosenStageLoopedCanonicalDiagramIso_corner n 1 1

/-- 終点射影は、同じ loop 像二族の指定厳密等式の同型そのもの。 -/
lemma commonChosenStageLoopedCanonicalDiagramIso_target (n : ℕ) :
    (commonChosenStageLoopedCanonicalDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) =
        eqToIso (congrArg
          (fun a : SimplicialNerve CommonObject.{u} ⟶ PointedKanInfinity ↦
            SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
          (commonChosenStageLoopedCanonicalFamily_target n).symm) :=
  d3IsFunctorEqIso_eqToIso (commonChosenStageLoopedCanonicalDiagramIso_target_isEq n)
    (commonChosenStageLoopedCanonicalFamily_target n).symm

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra

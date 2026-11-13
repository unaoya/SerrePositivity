module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexStrictification
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：標準単体上の一般の coherent な空間値図式を通常の Kan 値射列と比較する。
方針：標準単体と有限順序の nerve の同型を宇宙移送し、単体の strict 化を適用する。
規約：一般の底上の strict 化や境界固定の延長はこの段階では主張しない。
使われ方：Kerodon §5.6（Tag 027M）、straightening の局所比較を既存の strict 図式の API に接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：大きい標準単体は元の宇宙の有限順序の nerve の持ち上げと同型。
方針：標準単体の宇宙移送と、標準単体と有限順序の nerve の同型を合成する。
規約：有限順序の対象の宇宙は u、標準単体は u+1。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体と Kan 値射列の底を揃える。 -/
def localKanDiagramBaseIso (n : ℕ) :
    (Δ[n] : SSet.{u + 1}) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).symm ≪≫
    (SSet.uliftFunctor.{u + 1, u}).mapIso (stdSimplex.isoNerve n)

/-- 概要：Kan 値射列の coherent nerve 表示を標準単体へ戻すと、その豊穣射列の Yoneda 表示。
方針：普遍単体で両辺を評価し、有限順序の ULift の往復を消す。
規約：射列の各値は宇宙 u の Kan 複体。
使われ方：Kerodon §5.6（Tag 027M）、局所的な strict 化を既存の kanDiagramCoherentNerve に接続する。 -/
lemma localKanDiagramBaseIso_coherentNerve {n : ℕ}
    (F : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (localKanDiagramBaseIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram F) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 概要：coherent な空間値単体は通常の Kan 値射列の coherent nerve 表示と関手同型。
方針：単体の strict 化の終点を標準単体と有限順序の nerve の同型で表示し直す。
規約：対象ごとの同値ではなく標準単体上の図式全体の関手同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な局所図式を strict な図式の比較へ移す。 -/
noncomputable def localKanDiagramStrictificationIso {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm σ)
      ((localKanDiagramBaseIso n).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexStrictDiagram σ)) := by
  rw [localKanDiagramBaseIso_coherentNerve]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexStrictificationIso σ

/-- 概要：大きい標準単体からの任意の coherent な空間値写像を strict な Kan 値射列で表せる。
方針：写像の Yoneda 単体から通常の射列を取り出す。
規約：底の quasicategory 性などの追加条件は不要。
使われ方：Kerodon §5.6（Tag 027M）、任意の局所図式に適用する strict 化の存在形。 -/
lemma exists_localKanDiagramStrictification {n : ℕ} (F : (Δ[n] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F ((localKanDiagramBaseIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A)) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexStrictDiagram (SSet.yonedaEquiv F), ⟨?_⟩⟩
  have h := localKanDiagramStrictificationIso (SSet.yonedaEquiv F)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- 概要：小さい標準単体の持ち上げ上の任意の coherent な空間値図式は Kan 値射列の表示と関手同型。
方針：標準単体の宇宙移送で大きい単体へ移し、得た局所比較を元の底へ戻す。
規約：底の同型は元の宇宙の stdSimplex.isoNerve の持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening と底変換の API へ局所 strict 化を接続する。 -/
lemma exists_uliftLocalKanDiagramStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F
        ((SSet.uliftFunctor.{u + 1, u}).map (stdSimplex.isoNerve n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n
  obtain ⟨A, ⟨h⟩⟩ := exists_localKanDiagramStrictification (e.inv ≫ F)
  have h' := h.precomp e.hom
  have hb : e.hom ≫ (localKanDiagramBaseIso n).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (stdSimplex.isoNerve n).hom := by
    change e.hom ≫ (e.inv ≫ _) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h'
  rw [hb] at h'
  exact ⟨A, ⟨h'⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

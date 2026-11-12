module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalKanDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinityEquivalence

/-!
概要：標準単体上の一般の coherent な図式の小さい unstraightening を strict な図式の底変換で表す。
方針：局所的な図式の関手同型を小さい全空間の比較へ移し、厳密な底変換同型を続ける。
規約：同じ標準単体上の実際の比較射とその同値性を保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、局所的な strict 図式の全空間を比較の共通モデルにする。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい unstraightening の底変換同型は底への射影と可換。
方針：底変換の引き戻し四角形の標準同型の第二射影の公式を使う。
規約：底の写像 k は任意。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、関手同型の比較に続ける底上の射の条件。 -/
lemma smallLeftUnstraighteningBaseChangeIso_hom_snd {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (k : D ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) k =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection ((SSet.uliftFunctor.{u + 1, u}).map k ≫ F) :=
  IsPullback.isoPullback_hom_snd _

/-- 概要：底変換した図式との関手同型は小さい全空間から厳密な引き戻しへの底上の同値射を与える。
方針：小さい全空間の関手同型の比較射に、底変換の標準同型を合成する。
規約：底 D の quasicategory 性だけを追加する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、局所 strict 化を小さい fibration の実際の比較へ移す。 -/
lemma exists_smallLeftUnstraighteningComparison_of_baseChangeIso
    {B D : SSet.{u}} [Quasicategory D]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (k : D ⟶ B)
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F ((SSet.uliftFunctor.{u + 1, u}).map k ≫ G)) :
    ∃ f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) k,
      f ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) k =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  obtain ⟨f, hf, ef⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_smallLeftUnstraighteningComparison_of_functorIso η
  refine ⟨f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningBaseChangeIso G k).hom, ?_,
    ef.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningBaseChangeIso G k))⟩
  rw [Category.assoc, smallLeftUnstraighteningBaseChangeIso_hom_snd, hf]

/-- 概要：標準単体上の coherent な図式の小さい unstraightening は Kan 値射列の復元の底変換と同値。
方針：局所的な strict 化の関手同型を、全空間の比較射と底変換の同型へ移す。
規約：比較射は元の小さい標準単体を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な局所図式の小さい全空間を strict なモデルで表す。 -/
lemma exists_smallLocalUnstraighteningStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ∃ (A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
      (f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶
        pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A))
          (stdSimplex.isoNerve n).hom),
      f ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A))
        (stdSimplex.isoNerve n).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  obtain ⟨A, ⟨η⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_uliftLocalKanDiagramStrictification F
  obtain ⟨f, hf, ef⟩ := exists_smallLeftUnstraighteningComparison_of_baseChangeIso
    F (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A) (stdSimplex.isoNerve n).hom η
  exact ⟨A, f, hf, ef⟩

/-- 概要：標準単体上の小さい unstraightening は strict な Kan 値射列の復元の底変換と LF∞ 内で同型。
方針：構成済みの底上の前合成同値を coherent nerve の頂点の同型へ移す。
規約：全空間だけでなく同じ底上の fibration の ∞ 圏の比較。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、標準単体上で局所比較を貼り合わせるための対象での同型。 -/
lemma exists_smallLocalUnstraighteningVertexIso {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex
          (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A))
            (stdSimplex.isoNerve n).hom))) := by
  obtain ⟨A, f, hf, ef⟩ := exists_smallLocalUnstraighteningStrictification F
  exact ⟨A, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A))
      (stdSimplex.isoNerve n).hom) f hf ef⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

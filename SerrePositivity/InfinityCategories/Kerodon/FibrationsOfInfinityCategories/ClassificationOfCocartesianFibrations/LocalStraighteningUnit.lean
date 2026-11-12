module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallOppositeKanTransportUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalKanDiagramStrictification

/-!
概要：有限順序の nerve 上の任意の coherent な空間値図式の復元と straightening の単位。
方針：標準単体上の strictification を有限順序へ移し、strict 図式で構成した単位を同値不変性で戻す。
規約：ここでは各有限単体全体で比較する。境界上で指定した比較の延長は主張しない。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、一般の coherent な図式の分類へ進む局所的な復元比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：有限順序の nerve 上の任意の coherent Kan 値図式は strict な図式と関手同型。
方針：標準単体との標準同型で引き戻して strictify し、同型の逆で元の底へ戻す。
規約：元の底の頂点と宇宙を変えない。
使われ方：Kerodon §5.6.5（Tag 028U）、局所的な復元比較を strict な単位から構成する。 -/
lemma exists_finiteKanDiagramStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A)) := by
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (stdSimplex.isoNerve n)
  obtain ⟨A, ⟨h⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_uliftLocalKanDiagramStrictification (e.hom ≫ F)
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp h e.inv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ e.hom ≫ F) (e.inv ≫ e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A) at h'
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'
  exact ⟨A, ⟨h'⟩⟩

/-- 概要：有限順序の nerve 上の任意の coherent 空間値図式は、その小さい復元の straightening と関手同型。
方針：strictification、strict 図式での単位、復元候補の関手同型に関する不変性を合成する。
規約：対象ごとの fiber の同値ではなく、元の有限順序全体での関手同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、境界を保つ大域的な比較へ向けた局所の単位。 -/
noncomputable def finiteStraighteningUnitIso {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)) := by
  let A := (exists_finiteKanDiagramStrictification F).choose
  let h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve A) :=
    Classical.choice (exists_finiteKanDiagramStrictification F).choose_spec
  exact h ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanStraighteningUnitIso A ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallStraighteningCandidateIsoOfFunctorIso h.symm

/-- 概要：有限順序上の二つの coherent 図式の小さい復元が底上で同値なら元の図式は関手同型。
方針：両側の局所単位と、底上の同値に対する straightening 候補の不変性を合成する。
規約：与えた実際の底上の比較射を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、有限単体上の表現の同値類の一意性。 -/
noncomputable def finiteFunctorIsoOfUnstraighteningEquivalence {n : ℕ}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)
    (ef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  finiteStraighteningUnitIso F ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidateIsoOfPrecompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) f hf ef ≪≫
      (finiteStraighteningUnitIso G).symm

/-- 概要：有限順序上の二つの coherent 図式が関手同型であることは小さい復元の底上の同値で判定できる。
方針：順方向は構成済みの unstraightening の比較、逆方向は局所単位から得る関手同型を使う。
規約：写像空間の充満忠実性や境界を固定した比較の延長はこの判定には含めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、局所的な表現の存在方向と一意性を接続する。 -/
lemma finiteUnstraightening_equivalence_iff {n : ℕ}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) ↔
      ∃ f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G,
        f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  constructor
  · rintro ⟨η⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso η,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_projection η,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence η⟩
  · rintro ⟨f, hf, ef⟩
    exact ⟨finiteFunctorIsoOfUnstraighteningEquivalence f hf ef⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

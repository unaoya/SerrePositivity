module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinityEquivalence

/-!
概要：同じ底上の同値 span を、元の右脚との相対比較を保つ left fibration 間の同値射へ移す。
方針：相対前合成の本質的全射性で射を戻し、元の脚の同値性と二対三則で判定する。
規約：共通始域には inner fibration 性だけを要求する。新たな left fibration 仮定を置かない。
使われ方：under 切断の復元 span を、共同 straightening の分類比較へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の span の右脚を相対同型で回収する、底上の left fibration 間の同値射が存在する。 -/
lemma exists_leftFibrationComparison_of_span {X Y Z S : SSet.{u}} [Quasicategory S]
    (p : X ⟶ S) (q : Y ⟶ S) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (t : Z ⟶ S) [InnerFibration t] (a : Z ⟶ X) (b : Z ⟶ Y)
    (ha : a ≫ p = t) (hb : b ≫ q = t)
    (ea : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a) (eb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b) :
    ∃ (f : X ⟶ Y) (hf : f ≫ q = p), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t (a ≫ f) (by rw [Category.assoc, hf, ha]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t b hb)) := by
  have : Quasicategory X := quasicategory_of_innerFibration p
  have : Quasicategory Y := quasicategory_of_innerFibration q
  have : Quasicategory Z := quasicategory_of_innerFibration t
  let a' : Over.mk t ⟶ Over.mk p := Over.homMk a ha
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨hv⟩⟩ := he.choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t b hb)
  obtain ⟨f, hf, hfv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q p v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q a').app _ v) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t b hb) at hv
  rw [← hfv] at hv
  have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex q a' f hf
  have hrel : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t (a ≫ f) (by rw [Category.assoc, hf, ha]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q t b hb) :=
    (eqToIso (congrArg HomotopyCategory.mk hpre)).symm ≪≫ hv
  have hplain := hrel.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom Z).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ f) b at hplain
  have hef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := ea.cancel_left
    ((eb.isQCatEquivalence.ofFunctorIso hplain.symm).isPrecompositionEquivalence)
  exact ⟨f, hf, hef, ⟨hrel⟩⟩

/-- 同じ底上の span は、元の二つの left fibration の分類頂点の同型を与える。 -/
def leftFibrationVertexIsoOfSpan {X Y Z S : SSet.{u}} [Quasicategory S]
    (p : X ⟶ S) (q : Y ⟶ S) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (t : Z ⟶ S) [InnerFibration t] (a : Z ⟶ X) (b : Z ⟶ Y)
    (ha : a ≫ p = t) (hb : b ≫ q = t)
    (ea : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a) (eb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex q) := by
  let h := exists_leftFibrationComparison_of_span p q t a b ha hb ea eb
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q h.choose
    h.choose_spec.choose h.choose_spec.choose_spec.1

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

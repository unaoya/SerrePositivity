module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ReplacementEndCornerInner

/-!
概要：前合成同値の右持ち上げを持つ同値の、全境界持ち上げ。
方針：可逆 path 置換の標準切断を持ち上げ、元の射の厳密な切断を構成する。
規約：モデル構造の instance を仮定せず、充満忠実性と頂点全射性で判定する。
使われ方：比較四角形の終点側の比較を trivial Kan fibration に強める。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 前合成同値を右に持ち上げる同値には、厳密な切断が存在する。 -/
lemma IsQCatEquivalence.exists_section_of_kanEquivalenceLifting {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p
  have hj : j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p = 𝟙 X :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection p
  have : Mono j := by
    constructor
    intro Z a b hab
    have he := congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p) hab
    simpa only [Category.assoc, hj, Category.comp_id] using he
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence j := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p)).cancel_right
    rw [hj]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl X)).isQCatEquivalence
  have := hl j inferInstance he.isPrecompositionEquivalence
  have sq : CommSq (𝟙 X) j p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) := by
    constructor
    simpa only [Category.id_comp] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map p).symm
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) :=
    hp.equivalencePathReplacementMap_trivialKanFibration
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p)
  exact ⟨s ≫ sq.lift, by rw [Category.assoc, sq.fac_right, hs]⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (exists_section_of_kanEquivalenceLifting)


/-- 前合成同値を右に持ち上げる同値は、全ての境界を持ち上げる。 -/
lemma IsQCatEquivalence.trivialKanFibration_of_kanEquivalenceLifting {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  have := hl.innerFibration
  obtain ⟨s, hs⟩ := hp.exists_section_of_kanEquivalenceLifting hl
  apply hp.isFullyFaithful.trivialKanFibration_of_surjective
  intro y
  refine ⟨s.app (Opposite.op ⦋0⦌) y, ?_⟩
  exact congrArg (fun f : Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) y) hs

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (trivialKanFibration_of_kanEquivalenceLifting)


/-- 同値な横射と前合成同値を持ち上げる縦射の、終点比較は全境界を持ち上げる。 -/
lemma trivialKanFibration_replacementSquareEndCorner {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence v)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u v p q h) := by
  have ht := hv.equivalencePathReplacementMap_trivialKanFibration
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_fst _ _ ht.mem⟩
  have : Quasicategory (pullback q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) :=
    quasicategory_of_innerFibration (pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v))
  have he := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_isQCatEquivalence u v p q h hu hv
  exact he.trivialKanFibration_of_kanEquivalenceLifting
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.kanEquivalenceLifting_replacementSquareEndCorner u v p q h hp hq)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

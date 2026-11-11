module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan

/-!
概要：trivial Kan fibration は core の間でも trivial Kan fibration を誘導する。
方針：元の全単射の持ち上げを使い、充満忠実性による可逆辺の反映で core に戻す。
規約：始域・終域は quasicategory。モデル圏の仮定や因子分解は使わない。
使われ方：path 置換から元の圏への射影の core の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

/-- 概要：充満忠実な関手の下で core に入る図式は始域の core に持ち上がる。
方針：各一次単体の像の可逆性を充満忠実性で反映する。
規約：パラメータ T は任意の単体集合で、元の図式 f を厳密に保つ。
使われ方：trivial Kan fibration の持ち上げを core の持ち上げにする。 -/
def coreLiftOfFullyFaithful (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) {T : SSet.{u}}
    (f : T ⟶ X) (g : T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y : SSet.{u}))
    (h : f ≫ p = g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι) : T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift f (by
    intro s
    apply hp.reflects_isInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))
    have hh := congrArg (fun k : T ⟶ Y ↦ k.app (Opposite.op ⦋1⦌) s) h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map p))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (g.app (Opposite.op ⦋1⦌) s).val) hh).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (g.app (Opposite.op ⦋1⦌) s)))

/-- 概要：trivial Kan fibration の core の間の射も trivial Kan fibration。
方針：単射の持ち上げを元の圏で選び、可逆性の反映で core に持ち上げる。
規約：全ての単射に対する右持ち上げ性を直接証明する。
使われ方：可逆 path 置換の始域への射影の core の同値性。 -/
instance coreMap_trivialKanFibration (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) where
  mem := by
    intro A B j hj
    have : Mono j := hj
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) j hj
    constructor
    intro a b sq
    let sq' : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι) j p (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι) := by
      constructor
      rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc, sq.w, Category.assoc]
    let d := coreLiftOfFullyFaithful p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration p)
      sq'.lift b sq'.fac_right
    refine CommSq.HasLift.mk' { l := d, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι).mp
      change j ≫ d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι = _
      rw [← Category.assoc]
      change j ≫ sq'.lift = _
      exact sq'.fac_left
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι).mp
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc]
      change sq'.lift ≫ p = _
      exact sq'.fac_right

/-- 概要：可逆 path 置換の始域への射影の core は同値。
方針：射影の trivial Kan fibration 性を core に移し、同値を回収する。
規約：指定した元の射影の core 自体について述べる。
使われ方：全試験関手 core の引き戻し表示から置換を戻す。 -/
lemma corePathReplacementProjection_isQCatEquivalence (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleIdentity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：指定関手同型の三角等式を同じ頂点の成分へ写す。
方針：ホモトピー評価関手による同型の像の合成則を使う。
規約：元の指定同型の成分を選び直さない。
使われ方：共有セルでの成分 path の整合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ指定関手同型の成分は合成を保つ。 -/
lemma FunctorIso.app_trans {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {a b t : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (e ≪≫ k) x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app e x ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app k x := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso (e ≪≫ k) = e.toNatIso ≪≫ k.toNatIso := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso, Functor.mapIso_trans, Iso.trans_assoc,
      Iso.self_symm_id_assoc]
  exact congrArg (fun v ↦ v.app (SSet.HomotopyCategory.mk x)) hn

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (app_trans)


/-- 元の指定三角等式は、同じ頂点での指定成分の三角等式を与える。 -/
lemma IsoTriangleCommutes.app {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {a b t : X ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b} {k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a t}
    (h : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes e k d) (x : X _⦋0⦌) : e.app x ≪≫ k.app x = d.app x := by
  exact (FunctorIso.app_trans e k x).symm.trans
    (congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a t ↦ v.app x) h)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

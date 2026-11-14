module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleIdentity
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：充満忠実な後合成で指定三角等式を元の三辺へ反映する。
方針：三端点と指定像を照合し、同じ合成の像の等式を充満忠実性で反映する。
規約：指定された元の三辺と端点表示を保持する。
使われ方：局所 over 自然性の三角等式。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ三端点と指定像の照合後、充満忠実な後合成は三角等式を反映する。 -/
lemma IsFullyFaithful.reflectFunctorIsoTriangle_of_heq
    {X Y H : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {a b t : H ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a t)
    {a' b' t' : H ⟶ Y} (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' b') (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b' t')
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' t') (ha : a ≫ f = a') (hb : b ≫ f = b') (ht : t ≫ f = t')
    (he : HEq (e.postcomp f) E) (hk : HEq (k.postcomp f) K)
    (hd : HEq (d.postcomp f) D) (h : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes E K D) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes e k d := by
  apply hf.postcomp_functorIso_injective (e ≪≫ k) d
  have hp := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.iso_pasting_heq_of_endpoint_eq (e.postcomp f) (k.postcomp f) E K
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) ha)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) hb)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) ht) he.symm hk.symm
  exact eq_of_heq ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans e k f)).trans
    (hp.trans ((heq_of_eq h).trans hd.symm)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsFullyFaithful (reflectFunctorIsoTriangle_of_heq)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

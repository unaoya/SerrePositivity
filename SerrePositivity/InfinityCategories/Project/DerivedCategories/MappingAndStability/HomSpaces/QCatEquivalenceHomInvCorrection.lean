module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.QCatEquivalenceCoherentHomInv
/-!
概要：旧比較から coherent な比較への補正と恒等判定を明示する。
方針：指定された同型の値と関手 ∞ 圏の二胞体を保持する。
規約：古い比較との一致を先取りしない。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def QCatEquivalence.homInvCorrectionIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 X) (𝟙 X) := e.homInvIso.symm ≪≫ e.coherentHomInvIso

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (homInvCorrectionIso)

lemma QCatEquivalence.homInvCorrectionIso_factor {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.homInvIso ≪≫ e.homInvCorrectionIso = e.coherentHomInvIso := by
  simp only [homInvCorrectionIso, Iso.self_symm_id_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (homInvCorrectionIso_factor)

lemma QCatEquivalence.homInvCorrectionIso_eq_refl_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    e.homInvCorrectionIso = Iso.refl _ ↔ e.homInvIso = e.coherentHomInvIso := by
  constructor
  · intro h
    have he := e.homInvCorrectionIso_factor
    rw [h, Iso.trans_refl] at he
    exact he
  · intro h
    simp only [homInvCorrectionIso, h, Iso.symm_self_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence (homInvCorrectionIso_eq_refl_iff)

end
end SerrePositivity.InfinityCategories.Project.DerivedCategories

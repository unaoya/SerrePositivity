module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # 複体の次数ごと全射な semifree 解像度 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (S : Type u) [CommRing S]

/-- 概要：任意の複体は各次数全射な semifree 複体からの擬同型を持つ。
方針：一点 dg 加群の解像度を評価し、全射性と擬同型性を転送する。
規約：非有界複体であり有界性や有限生成性を仮定しない。
使われ方：semifree 導来比較の本質的全射性。 -/
theorem exists_complexSemifree_resolution (M : Complex S) :
    ∃ (P : Complex S) (q : P ⟶ M),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P ∧ (∀ n : ℤ, Function.Surjective (q.f n)) ∧ QuasiIso q := by
  obtain ⟨P, q, hP, hq, hW⟩ := exists_semifree_resolution S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S M))
  exact ⟨(ringModuleEquivalence S).functor.obj P,
    (ringModuleEquivalence S).functor.map q,
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation S P).mpr hP,
    fun n => hq PUnit.unit n, (ringModuleQuasiIso_iff S q).mp hW⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories

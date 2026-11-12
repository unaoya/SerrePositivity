module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexInvertingRestriction
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：指定辺を反転する条件の、単体圏の貼り合わせに関する局所性。
方針：指定辺の条件を初頂点座標で判定し、pushout の両脚の全射性を使う。
規約：底と標的の quasicategory 性は不要。
使われ方：反転関手の部分複体の pullback による貼り合わせ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 指定辺の条件は、任意の一次単体の初頂点座標で判定できる。 -/
lemma transportSimplexInitialEdges_mem_iff {B : SSet.{u}}
    (s : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) _⦋1⦌) :
    s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B ↔
      (s.hom.down.hom.unop.toOrderHom 0).val = 0 := by
  constructor
  · rintro ⟨i, j, f, hf, he⟩
    have hv := congrArg (fun t : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) 1 ↦
      (t.hom.down.hom.unop.toOrderHom 0).val) he
    rw [← hv]
    exact congrArg Fin.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexPreservesFirst_iff f).mp hf)
  · intro h
    refine ⟨s.obj 0, s.obj 1, s.hom, ?_, ComposableArrows.mk₁_hom s⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexPreservesFirst_iff s.hom).mpr
    exact Fin.ext h

/-- 底の任意の射は、一次単体の指定辺への所属を保ち反映する。 -/
lemma transportSimplexInitialEdges_map_iff {B D : SSet.{u}} (f : B ⟶ D)
    (s : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) _⦋1⦌) :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)).app (Opposite.op ⦋1⦌) s ∈
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges D ↔ s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B := by
  rw [transportSimplexInitialEdges_mem_iff, transportSimplexInitialEdges_mem_iff]
  rfl

/-- 合成が反転する辺は、最初の射で写した辺を次の射が反転する条件に等しい。 -/
lemma invertedEdges_comp_iff {X Y E : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ E)
    (s : X _⦋1⦌) :
    s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (f ≫ g) ↔ f.app (Opposite.op ⦋1⦌) s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl

/-- 単体圏の nerve の pushout では、指定辺を反転する条件は両脚から回収できる。 -/
lemma transportSimplexInvertsEdges_of_isPushout {A B C D E : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor i))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor g)) (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor j))) (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges D) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k) ≫ U) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor j) ≫ U) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges C) := by
  constructor
  · intro hU
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertsEdges_restrict k U hU,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertsEdges_restrict j U hU⟩
  · rintro ⟨hB, hC⟩ s hs
    obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := Types.eq_or_eq_of_isPushout (h.app (Opposite.op ⦋1⦌)) s
    · exact (invertedEdges_comp_iff _ U t).mp
        (hB ((transportSimplexInitialEdges_map_iff k t).mp hs))
    · exact (invertedEdges_comp_iff _ U t).mp
        (hC ((transportSimplexInitialEdges_map_iff j t).mp hs))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalHomCriterion

/-!
概要：小さい辺族の局所対象を、元の生成辺と全パラメータ Hom で判定する。
方針：N の局所性を再利用し、生成族の range を展開する。
規約：反射・局所置換の存在を仮定せず、指定辺と全単体集合パラメータを保持する。
使われ方：P-1 f1、HTT 5.5.4.1 の小生成な局所化の入口。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Generators


variable {X : SSet.{v}} [Quasicategory X] {I : Type u}

/-- 小さい生成族に対する局所性は、元の各生成辺で判定できる。 -/
lemma isLocalObject_range_iff (edges : I → X _⦋1⦌) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) z ↔ ∀ i,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (edges i))) z := by
  constructor
  · intro h i
    exact h (edges i) ⟨i, rfl⟩
  · rintro h e ⟨i, rfl⟩
    exact h i

/-- 生成族の局所性は任意単体集合パラメータの元の前合成の全単射性と同値。 -/
lemma isLocalObject_range_iff_constantHom_bijective
    (edges : I → X _⦋1⦌) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) z ↔ ∀ i (A : SSet.{v}),
      Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X (X.δ 0 (edges i)) z ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A
          (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (edges i))) ≫ α) := by
  rw [isLocalObject_range_iff]
  exact forall_congr' fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_constantHom_bijective _

/-- 同じ局所対象への全パラメータ前合成で S-局所同値を判定する。 -/
lemma localEquivalenceHom_range_iff_constantHom_bijective
    (edges : I → X _⦋1⦌) {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom (Set.range edges) f ↔
      ∀ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) z →
        ∀ A : SSet.{v}, Function.Bijective
          (fun α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X y z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A f ≫ α) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom
  exact forall_congr' fun z ↦ imp_congr_right fun _ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_constantHom_bijective f

/-- 一方の生成辺が他方の局所同値なら、局所対象の包含が従う。 -/
lemma localObjects_antitone_of_generators_localEquivalences
    {W V : Set (X _⦋1⦌)} (h : W ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V) {z : X _⦋0⦌}
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject V z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z := by
  intro e he
  exact h he z hz

/-- 生成辺の包含を局所同値への包含に弱めても、局所同値全体は単調。 -/
lemma localEquivalences_subset_of_generators_localEquivalences
    {W V : Set (X _⦋1⦌)} (h : W ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V := by
  intro e he z hz
  exact he z (localObjects_antitone_of_generators_localEquivalences h hz)

/-- 二つの生成系が同じ局所同値を与えることは、相互の生成辺だけで判定できる。 -/
lemma localEquivalences_eq_iff_generators (W V : Set (X _⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V ↔
      W ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V ∧ V ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  constructor
  · intro h
    exact ⟨h ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.subset_localEquivalences W, h.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.subset_localEquivalences V⟩
  · rintro ⟨hWV, hVW⟩
    exact Set.Subset.antisymm
      (localEquivalences_subset_of_generators_localEquivalences hWV)
      (localEquivalences_subset_of_generators_localEquivalences hVW)

/-- 局所対象の条件が一致することと、局所同値全体の一致は同値。 -/
lemma localEquivalences_eq_iff_localObjects (W V : Set (X _⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences V ↔
      ∀ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject V z := by
  constructor
  · intro h z
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalObject_localEquivalences_iff W z,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalObject_localEquivalences_iff V z, h]
  · intro h
    apply Set.ext
    intro e
    constructor <;> intro he z hz
    · exact he z ((h z).mpr hz)
    · exact he z ((h z).mp hz)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Generators

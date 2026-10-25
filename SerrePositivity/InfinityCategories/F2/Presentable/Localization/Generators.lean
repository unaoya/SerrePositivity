module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalEquivalences
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalHomCriterion

/-!
概要：小さい辺族の局所対象を、元の生成辺と全パラメータ Hom で判定する。
方針：N の局所性を再利用し、生成族の range を展開する。
規約：反射・局所置換の存在を仮定せず、指定辺と全単体集合パラメータを保持する。
使われ方：P-1 f1、HTT 5.5.4.1 の小生成な局所化の入口。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

variable {X : SSet.{v}} [Quasicategory X] {I : Type u}

/-- 小さい生成族に対する局所性は、元の各生成辺で判定できる。 -/
lemma isLocalObject_range_iff (edges : I → X _⦋1⦌) (z : X _⦋0⦌) :
    IsLocalObject (Set.range edges) z ↔ ∀ i,
      IsLocalForHom (Truncated.HomotopyCategory.homMk (edgeOfSimplex (edges i))) z := by
  constructor
  · intro h i
    exact h (edges i) ⟨i, rfl⟩
  · rintro h e ⟨i, rfl⟩
    exact h i

/-- 生成族の局所性は任意単体集合パラメータの元の前合成の全単射性と同値。 -/
lemma isLocalObject_range_iff_constantHom_bijective
    (edges : I → X _⦋1⦌) (z : X _⦋0⦌) :
    IsLocalObject (Set.range edges) z ↔ ∀ i (A : SSet.{v}),
      Function.Bijective (fun α : ConstantFunctorHom A X (X.δ 0 (edges i)) z ↦
        constantFunctorHomMap A
          (Truncated.HomotopyCategory.homMk (edgeOfSimplex (edges i))) ≫ α) := by
  rw [isLocalObject_range_iff]
  exact forall_congr' fun i ↦ isLocalForHom_iff_constantHom_bijective _

/-- 同じ局所対象への全パラメータ前合成で S-局所同値を判定する。 -/
lemma localEquivalenceHom_range_iff_constantHom_bijective
    (edges : I → X _⦋1⦌) {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    LocalEquivalenceHom (Set.range edges) f ↔
      ∀ z : X _⦋0⦌, IsLocalObject (Set.range edges) z →
        ∀ A : SSet.{v}, Function.Bijective
          (fun α : ConstantFunctorHom A X y z ↦ constantFunctorHomMap A f ≫ α) := by
  unfold LocalEquivalenceHom
  exact forall_congr' fun z ↦ imp_congr_right fun _ ↦
    isLocalForHom_iff_constantHom_bijective f

/-- 一方の生成辺が他方の局所同値なら、局所対象の包含が従う。 -/
lemma localObjects_antitone_of_generators_localEquivalences
    {W V : Set (X _⦋1⦌)} (h : W ⊆ localEquivalences V) {z : X _⦋0⦌}
    (hz : IsLocalObject V z) : IsLocalObject W z := by
  intro e he
  exact h he z hz

/-- 生成辺の包含を局所同値への包含に弱めても、局所同値全体は単調。 -/
lemma localEquivalences_subset_of_generators_localEquivalences
    {W V : Set (X _⦋1⦌)} (h : W ⊆ localEquivalences V) :
    localEquivalences W ⊆ localEquivalences V := by
  intro e he z hz
  exact he z (localObjects_antitone_of_generators_localEquivalences h hz)

/-- 二つの生成系が同じ局所同値を与えることは、相互の生成辺だけで判定できる。 -/
lemma localEquivalences_eq_iff_generators (W V : Set (X _⦋1⦌)) :
    localEquivalences W = localEquivalences V ↔
      W ⊆ localEquivalences V ∧ V ⊆ localEquivalences W := by
  constructor
  · intro h
    exact ⟨h ▸ subset_localEquivalences W, h.symm ▸ subset_localEquivalences V⟩
  · rintro ⟨hWV, hVW⟩
    exact Set.Subset.antisymm
      (localEquivalences_subset_of_generators_localEquivalences hWV)
      (localEquivalences_subset_of_generators_localEquivalences hVW)

/-- 局所対象の条件が一致することと、局所同値全体の一致は同値。 -/
lemma localEquivalences_eq_iff_localObjects (W V : Set (X _⦋1⦌)) :
    localEquivalences W = localEquivalences V ↔
      ∀ z : X _⦋0⦌, IsLocalObject W z ↔ IsLocalObject V z := by
  constructor
  · intro h z
    rw [← isLocalObject_localEquivalences_iff W z,
      ← isLocalObject_localEquivalences_iff V z, h]
  · intro h
    apply Set.ext
    intro e
    constructor <;> intro he z hz
    · exact he z ((h z).mpr hz)
    · exact he z ((h z).mp hz)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization

module
public import SerrePositivity.DifferentialGraded.Module.Biproduct
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Module.Yoneda

/-! # 指定生成元からの有限cellの構成データ

対象宇宙は縮小せず、有限操作の木と生成元への依存を保持する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表加群から有限回の和・shift・cone・同型で作った証明付きcell。 -/
inductive ModuleFiniteCellCode (S : Set D) : ModuleCategory A D → Type (max (u + 1) v)
  | zero : ModuleFiniteCellCode S (moduleZero A D)
  | generator (x : D) (hx : x ∈ S) :
      ModuleFiniteCellCode S (ForgetEnrichment.of (Complex A) (representable A x))
  | shift {M : ModuleCategory A D} (s : ℤ) (c : ModuleFiniteCellCode S M) :
      ModuleFiniteCellCode S (M⟦s⟧)
  | sum {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M)
      (d : ModuleFiniteCellCode S N) : ModuleFiniteCellCode S (moduleBiprod A D M N)
  | cone {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M)
      (d : ModuleFiniteCellCode S N) (f : M ⟶ N) : ModuleFiniteCellCode S (moduleCone A D f)
  | iso {M N : ModuleCategory A D} (c : ModuleFiniteCellCode S M) (e : M ≅ N) :
      ModuleFiniteCellCode S N

namespace ModuleFiniteCellCode
variable {A D} {S T : Set D}

/-- 生成元の集合を大きくしても同じ有限操作の木を使える。 -/
def mono (h : S ⊆ T) {M : ModuleCategory A D} :
    ModuleFiniteCellCode A D S M → ModuleFiniteCellCode A D T M
  | .zero => .zero
  | .generator x hx => .generator x (h hx)
  | .shift s c => .shift s (c.mono h)
  | .sum c d => .sum (c.mono h) (d.mono h)
  | .cone c d f => .cone (c.mono h) (d.mono h) f
  | .iso c e => .iso (c.mono h) e

/-- 操作木に現れる節点数。任意の同型による輸送も一操作として数える。 -/
def size {M : ModuleCategory A D} : ModuleFiniteCellCode A D S M → ℕ
  | .zero => 1
  | .generator _ _ => 1
  | .shift _ c => c.size + 1
  | .sum c d => c.size + d.size + 1
  | .cone c d _ => c.size + d.size + 1
  | .iso c _ => c.size + 1

/-- 操作木に実際に現れる有限個の代表生成元。 -/
noncomputable def support {M : ModuleCategory A D} : ModuleFiniteCellCode A D S M → Finset D := by
  classical
  exact fun c => match c with
    | .zero => ∅
    | .generator x _ => {x}
    | .shift _ c => c.support
    | .sum c d => c.support ∪ d.support
    | .cone c d _ => c.support ∪ d.support
    | .iso c _ => c.support

lemma support_subset {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    (↑c.support : Set D) ⊆ S := by
  classical
  induction c with
  | zero => simp [support]
  | generator x hx => simpa only [support, Finset.coe_singleton, Set.singleton_subset_iff] using hx
  | shift s c ih => exact ih
  | sum c d ihc ihd =>
    simpa only [support, Finset.coe_union] using Set.union_subset ihc ihd
  | cone c d f ihc ihd =>
    simpa only [support, Finset.coe_union] using Set.union_subset ihc ihd
  | iso c e ih => exact ih

/-- 同じ対象を、操作木に現れる有限個の生成元だけで構成し直す。 -/
noncomputable def restrictSupport {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    ModuleFiniteCellCode A D (↑c.support : Set D) M := by
  classical
  induction c with
  | zero => exact .zero
  | generator x hx => exact .generator x (by simp [support])
  | shift s c ih => exact .shift s ih
  | sum c d ihc ihd =>
    exact .sum (ihc.mono (by intro x hx; exact Finset.mem_union_left _ hx))
      (ihd.mono (by intro x hx; exact Finset.mem_union_right _ hx))
  | cone c d f ihc ihd =>
    exact .cone (ihc.mono (by intro x hx; exact Finset.mem_union_left _ hx))
      (ihd.mono (by intro x hx; exact Finset.mem_union_right _ hx)) f
  | iso c e ih => exact .iso ih e

end ModuleFiniteCellCode

/-- 指定集合の代表加群から有限回の操作で構成できる性質。 -/
def moduleFiniteCellOver (S : Set D) : ObjectProperty (ModuleCategory A D) :=
  fun M => Nonempty (ModuleFiniteCellCode A D S M)

/-- すべての代表加群を生成元として許したfinite cell。 -/
def moduleFiniteCell : ObjectProperty (ModuleCategory A D) := moduleFiniteCellOver A D Set.univ

lemma moduleFiniteCellOver_mono {S T : Set D} (h : S ⊆ T) {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleFiniteCellOver A D T M := by
  obtain ⟨c⟩ := hM
  exact ⟨c.mono h⟩

/-- 各finite cellは有限個の指定生成元だけに依存する。 -/
lemma moduleFiniteCellOver_iff_finite_generators (S : Set D) (M : ModuleCategory A D) :
    moduleFiniteCellOver A D S M ↔ ∃ t : Finset D, (↑t : Set D) ⊆ S ∧
      moduleFiniteCellOver A D (↑t : Set D) M := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.support, c.support_subset, ⟨c.restrictSupport⟩⟩
  · rintro ⟨t, ht, hM⟩
    exact moduleFiniteCellOver_mono A D ht hM

lemma moduleFiniteCellOver_zero (S : Set D) : moduleFiniteCellOver A D S (moduleZero A D) :=
  ⟨.zero⟩

lemma moduleFiniteCellOver_representable {S : Set D} (x : D) (hx : x ∈ S) :
    moduleFiniteCellOver A D S (ForgetEnrichment.of (Complex A) (representable A x)) :=
  ⟨.generator x hx⟩

lemma moduleFiniteCellOver_shift {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (s : ℤ) : moduleFiniteCellOver A D S (M⟦s⟧) := by
  obtain ⟨c⟩ := hM
  exact ⟨.shift s c⟩

lemma moduleFiniteCellOver_biprod {S : Set D} {M N : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (hN : moduleFiniteCellOver A D S N) :
    moduleFiniteCellOver A D S (moduleBiprod A D M N) := by
  obtain ⟨c⟩ := hM
  obtain ⟨d⟩ := hN
  exact ⟨.sum c d⟩

lemma moduleFiniteCellOver_cone {S : Set D} {M N : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (hN : moduleFiniteCellOver A D S N) (f : M ⟶ N) :
    moduleFiniteCellOver A D S (moduleCone A D f) := by
  obtain ⟨c⟩ := hM
  obtain ⟨d⟩ := hN
  exact ⟨.cone c d f⟩

lemma moduleFiniteCellOver_of_iso {S : Set D} {M N : ModuleCategory A D}
    (e : M ≅ N) (hM : moduleFiniteCellOver A D S M) : moduleFiniteCellOver A D S N := by
  obtain ⟨c⟩ := hM
  exact ⟨.iso c e⟩

instance moduleFiniteCellOverClosedUnderIso (S : Set D) :
    (moduleFiniteCellOver A D S).IsClosedUnderIsomorphisms where
  of_iso := moduleFiniteCellOver_of_iso A D

lemma moduleFiniteCell_representable (x : D) :
    moduleFiniteCell A D (ForgetEnrichment.of (Complex A) (representable A x)) :=
  moduleFiniteCellOver_representable A D x (Set.mem_univ x)

lemma moduleFiniteCell_iff_finite_generators (M : ModuleCategory A D) :
    moduleFiniteCell A D M ↔ ∃ t : Finset D, moduleFiniteCellOver A D (↑t : Set D) M := by
  constructor
  · intro hM
    obtain ⟨t, _, ht⟩ := (moduleFiniteCellOver_iff_finite_generators A D Set.univ M).1 hM
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact moduleFiniteCellOver_mono A D (Set.subset_univ _) ht

end SerrePositivity.DifferentialGraded

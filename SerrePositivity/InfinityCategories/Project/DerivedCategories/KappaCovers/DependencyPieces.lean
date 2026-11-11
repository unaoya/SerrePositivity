module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
概要：可算な依存先を保つ κ-small なラベル部分集合で、元のラベルを被覆する。
方針：依存閉包を可算段階で取り、正則性で濃度を評価する。
規約：ラベルの小ささだけの主張。実加群の部分対象と余極限は別に構成する。
使われ方：D-8 d の cell ラベルを制限する κ-filtered 添字。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory SSet
variable {A : Type u} (dep : A → Set A) {κ : Cardinal.{u}} [Fact κ.IsRegular]

def dgKappaDependencyStage (s : Set A) : ℕ → Set A
  | 0 => s
  | n + 1 => dgKappaDependencyStage s n ∪ ⋃ a : dgKappaDependencyStage s n, dep a.val

def dgKappaDependencyClosure (s : Set A) : Set A :=
  ⋃ n : ULift.{u} ℕ, dgKappaDependencyStage dep s n.down

lemma dgKappaDependencyStage_small (hκ : Cardinal.aleph0 < κ)
    (hdep : ∀ a, HasCardinalLT (dep a) κ) {s : Set A} (hs : HasCardinalLT s κ) (n : ℕ) :
    HasCardinalLT (dgKappaDependencyStage dep s n) κ := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact hasCardinalLT_union hκ.le ih (hasCardinalLT_iUnion _ ih (fun a => hdep a.val))

lemma dgKappaDependencyClosure_small (hκ : Cardinal.aleph0 < κ)
    (hdep : ∀ a, HasCardinalLT (dep a) κ) {s : Set A} (hs : HasCardinalLT s κ) :
    HasCardinalLT (dgKappaDependencyClosure dep s) κ := by
  have hn : HasCardinalLT (ULift.{u} ℕ) κ := by
    apply (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hκ
  exact hasCardinalLT_iUnion _ hn
    (fun n => dgKappaDependencyStage_small dep hκ hdep hs n.down)

lemma dgKappaDependencyClosure_contains (s : Set A) : s ⊆ dgKappaDependencyClosure dep s :=
  Set.subset_iUnion (fun n : ULift.{u} ℕ => dgKappaDependencyStage dep s n.down) ⟨0⟩

lemma dgKappaDependencyClosure_closed (s : Set A) {a : A}
    (ha : a ∈ dgKappaDependencyClosure dep s) : dep a ⊆ dgKappaDependencyClosure dep s := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  intro b hb
  apply Set.mem_iUnion.mpr
  refine ⟨⟨n.down + 1⟩, Or.inr ?_⟩
  exact Set.mem_iUnion.mpr ⟨⟨a, hn⟩, hb⟩

def DGKappaDependencyPieces :=
  {s : Set A // HasCardinalLT s κ ∧ ∀ a ∈ s, dep a ⊆ s}

instance : PartialOrder (DGKappaDependencyPieces dep (κ := κ)) :=
  inferInstanceAs (PartialOrder {s : Set A // HasCardinalLT s κ ∧ ∀ a ∈ s, dep a ⊆ s})

lemma dgKappaDependencyPieces_isCardinalFiltered :
    IsCardinalFiltered (DGKappaDependencyPieces dep (κ := κ)) κ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' := (hasCardinalLT_iff_cardinal_mk_lt K κ).mpr hK
  refine ⟨⟨⋃ k, (f k).val, hasCardinalLT_iUnion _ hK' (fun k => (f k).property.1), ?_⟩, ?_⟩
  · intro a ha b hb
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨k, (f k).property.2 a hk hb⟩
  · intro k
    change (f k).val ⊆ ⋃ k, (f k).val
    exact Set.subset_iUnion (fun j : K => (f j).val) k

lemma dgKappaDependencyPieces_nerve_isKappaFiltered :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve (DGKappaDependencyPieces dep (κ := κ))) := by
  haveI := dgKappaDependencyPieces_isCardinalFiltered dep (κ := κ)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

lemma dgKappaDependencyPieces_cover (hκ : Cardinal.aleph0 < κ)
    (hdep : ∀ a, HasCardinalLT (dep a) κ) (a : A) :
    ∃ s : DGKappaDependencyPieces dep (κ := κ), a ∈ s.val := by
  have hs : HasCardinalLT ({a} : Set A) κ := hasCardinalLT_of_finite _ _ hκ.le
  exact ⟨⟨dgKappaDependencyClosure dep {a}, dgKappaDependencyClosure_small dep hκ hdep hs,
    fun _ ha => dgKappaDependencyClosure_closed dep {a} ha⟩,
    dgKappaDependencyClosure_contains dep {a} (Set.mem_singleton a)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers

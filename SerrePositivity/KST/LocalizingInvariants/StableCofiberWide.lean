module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HigherHornEdgeCover
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornEdges
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
概要：指定安定閉包に cofiber を持つ辺だけからなる wide 部分複体を構成する。
方針：全単体の全辺条件を定義し、二次内ホーンは二対三性、高次は辺の被覆で充填する。
規約：retract 閉包に置き換えない。SConstruction を import しない。
使われ方：Sp-7 の元の本質像に沿う亜群化の離散性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 概要：全単体で、全ての退化辺を含む全辺の所属を要求する部分複体。
方針：全単体の全辺条件を定義し、二次内ホーンは二対三性、高次は辺の被覆で充填する。
規約：retract 閉包に置き換えない。SConstruction を import しない。
使われ方：Sp-7 の元の本質像に沿う亜群化の離散性。 -/
def edgewiseSubcomplex {X : SSet.{u}} (W : Set (X _⦋1⦌)) : X.Subcomplex where
  obj n := {s | ∀ θ : ⦋1⦌ ⟶ n.unop, X.map θ.op s ∈ W}
  map {n m} φ s hs θ := by
    have ht := hs (θ ≫ φ.unop)
    change X.map (φ ≫ θ.op) s ∈ W at ht
    simpa only [Functor.map_comp, types_comp_apply] using ht

/-- 概要：指定安定閉包に cofiber を持つ元の辺の wide 部分複体。
方針：全単体の全辺条件を定義し、二次内ホーンは二対三性、高次は辺の被覆で充填する。
規約：retract 閉包に置き換えない。SConstruction を import しない。
使われ方：Sp-7 の元の本質像に沿う亜群化の離散性。 -/
def stableCofiberWide {X : SSet.{u}} (P : Set (X _⦋0⦌)) : X.Subcomplex :=
  edgewiseSubcomplex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x})

@[simp] lemma stableCofiberWide_mem {X : SSet.{u}} (P : Set (X _⦋0⦌))
    (n : ℕ) (s : X _⦋n⦌) :
    s ∈ (stableCofiberWide P).obj (Opposite.op ⦋n⦌) ↔
      ∀ θ : ⦋1⦌ ⟶ ⦋n⦌,
        X.map θ.op s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x} := Iff.rfl

/-- 概要：二対三性と高次ホーンの全辺被覆により、同じ wide 包含は inner fibration。
方針：全単体の全辺条件を定義し、二次内ホーンは二対三性、高次は辺の被覆で充填する。
規約：retract 閉包に置き換えない。SConstruction を import しない。
使われ方：Sp-7 の元の本質像に沿う亜群化の離散性。 -/
instance stableCofiberWide_innerFibration {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (P : Set (X _⦋0⦌)) : InnerFibration (stableCofiberWide P).ι where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      have hknown (e : (horn (n + 2) i : SSet.{u}) _⦋1⦌) :
          b.app (Opposite.op ⦋1⦌) e.val ∈
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x} := by
        have he := congrArg (fun f => f.app (Opposite.op ⦋1⦌) e) sq.w
        change (a.app (Opposite.op ⦋1⦌) e).val = b.app (Opposite.op ⦋1⦌) e.val at he
        rw [← he]
        simpa using
          (a.app (Opposite.op ⦋1⦌) e).property (𝟙 ⦋1⦌)
      have hedge (e : (Δ[n + 2] : SSet.{u}) _⦋1⦌) :
          b.app (Opposite.op ⦋1⦌) e ∈
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x} := by
        cases n with
        | zero =>
          have hi : i = 1 := by
            apply Fin.ext
            change 0 < i.val at h0
            change i.val < 2 at hn
            change i.val = 1
            omega
          subst i
          by_cases he : e ∈ (horn 2 1).obj (Opposite.op ⦋1⦌)
          · exact hknown ⟨e, he⟩
          · rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.innerTwoHorn_missing_edge_eq_long e he]
            have hleft := hknown (horn.face (1 : Fin 3) 2 (by decide))
            have hright := hknown (horn.face (1 : Fin 3) 0 (by decide))
            have ht := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_twoOfThree P b).1
            simpa only [SSet.yonedaEquiv_comp] using ht hleft hright
        | succ n =>
          obtain ⟨e', he'⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horn_ι_edge_surjective_of_three_le (by omega) i e
          exact he' ▸ hknown e'
      let l : (Δ[n + 2] : SSet.{u}) ⟶ (stableCofiberWide P : SSet.{u}) := {
        app := fun m => ↾fun s => ⟨b.app m s, fun θ => by
          rw [← b.naturality_apply θ.op]
          exact hedge _⟩
        naturality := fun {_ _} φ => by
          apply ConcreteCategory.hom_ext
          intro s
          apply Subtype.ext
          exact b.naturality_apply φ s }
      refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
      · apply (cancel_mono (stableCofiberWide P).ι).1
        rw [Category.assoc]
        exact sq.w.symm
      · rfl

/-- 概要：同じ元の部分複体は quasicategory である。
方針：全単体の全辺条件を定義し、二次内ホーンは二対三性、高次は辺の被覆で充填する。
規約：retract 閉包に置き換えない。SConstruction を import しない。
使われ方：Sp-7 の元の本質像に沿う亜群化の離散性。 -/
instance stableCofiberWide_quasicategory {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (P : Set (X _⦋0⦌)) : Quasicategory (stableCofiberWide P : SSet.{u}) :=
  quasicategory_of_innerFibration (stableCofiberWide P).ι

end SerrePositivity.KST.LocalizingInvariants

module

public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits

/-!
概要：Noether基底の閉集合上の普遍Čech降下性を帰納の述語にする。
方針：閉埋め込みの像を指定し、空の像では元の射が同型になることを使う。
規約：基底の閉部分の構造を選び直さず、全ての閉埋め込みを量化する。
使われ方：閉像の帰納（承認済み計画I07・I08）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/-- 指定した閉像を持つ全ての閉埋め込み上の固有全射の普遍Čech降下性。 -/
def NoetherClosedPerfectCechProperty (S : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds S) : Prop :=
  ∀ (Y : Scheme.{u}) (j : Y ⟶ S), IsClosedImmersion j →
    Set.range j = (C : Set S) →
    ∀ (X : Scheme.{u}) (f : X ⟶ Y), IsProper f → Surjective f →
      PerfectCechUniversalDescent p hp f

/-- 空の閉像では、終域が空であるため同型の降下性へ帰着する。 -/
theorem noetherClosedPerfectCechProperty_empty
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp ⊥ := by
  intro Y j hj hr X f hf hs
  haveI : IsEmpty Y := ⟨fun y ↦ by
    have hy : j y ∈ Set.range j := Set.mem_range_self y
    rw [hr] at hy
    exact hy⟩
  haveI : IsIso f := inferInstance
  exact perfectCechUniversalDescent_flat_surjective p hp f

end SerrePositivity.AlgebraicGeometry

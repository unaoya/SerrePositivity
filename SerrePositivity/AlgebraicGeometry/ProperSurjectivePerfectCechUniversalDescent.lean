module

public import SerrePositivity.AlgebraicGeometry.NoetherClosedPerfectCechStep
public import Mathlib.Topology.NoetherianSpace

/-!
概要：Noether閉像の帰納を閉じ、Noetherアフィン基底上の固有全射へ戻す。
方針：閉集合の真の包含の整礎性と、基底自身の恒等閉埋め込みを使う。
規約：全てのNoether試験基底と被覆を含む元の普遍降下性を結論とする。
使われ方：有限表示なaffine v被覆の判定（承認済み計画I11・I12）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/-- Noether閉集合の真の包含による帰納を閉じる。 -/
theorem noetherClosedPerfectCechProperty_all
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R))) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp C := by
  refine wellFounded_lt.induction C ?_
  intro D ih
  exact noetherClosedPerfectCechProperty_step p hp D ih

/-- Noetherアフィン基底上の元の固有全射は、完全構造層の普遍Čech降下性を持つ。 -/
theorem properSurjective_perfectCechUniversalDescent
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Surjective f]
    (p : ℕ) (hp : p.Prime) : PerfectCechUniversalDescent p hp f := by
  have h := noetherClosedPerfectCechProperty_all (R := R) p hp ⊤
  exact h (Spec (CommRingCat.of R)) (𝟙 _) inferInstance
    (by ext x; simp) X f inferInstance inferInstance

end SerrePositivity.AlgebraicGeometry

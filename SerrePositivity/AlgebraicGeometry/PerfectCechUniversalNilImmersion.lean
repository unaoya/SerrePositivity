module

public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalNilReflection
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
概要：全射な閉埋め込みに完全構造層の普遍Čech降下性を供給する。
方針：自己底変換の同型に平坦降下を使い、既存のnil閉厚化の反映で戻す。
規約：元の署名の有限表示と全射性を保持し、係数や基底を変えない。
使われ方：被約化とNoether閉像の帰納（承認済み計画D04）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- 全射な有限表示の閉埋め込みは、完全構造層の普遍Čech降下性を持つ。 -/
theorem perfectCechUniversalDescent_nilImmersion
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] [LocallyOfFinitePresentation f] :
    PerfectCechUniversalDescent p hp f := by
  apply perfectCechUniversalDescent_of_nil_baseChange p hp f f
  exact perfectCechUniversalDescent_flat_surjective p hp (pullback.snd f f)

end SerrePositivity.AlgebraicGeometry

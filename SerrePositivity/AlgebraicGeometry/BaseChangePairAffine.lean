module

public import SerrePositivity.AlgebraicGeometry.CartesianPullbackComparison
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
概要：制限した源の底変換を、底変換した二つの源の交叉として比較する。
方針：二つの Cartesian な比較の交叉の正方形から、実際の同型を取る。
規約：構造射は実際の射として保持し、基底射に忠実平坦性を要求しない。
使われ方：C04 の一般の標的の有限 affine 被覆上での affine 性の降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X V S T : Scheme.{u}}

/-- 二つの源の交叉の底変換と、底変換した源の交叉との具体的な同型。 -/
def baseChangePairIso (p : X ⟶ S) (q : V ⟶ S) (g : T ⟶ S) :
    pullback (pullback.snd p g) (pullback.snd q g) ≅ pullback (pullback.fst p q ≫ p) g :=
  (isPullback_cartesianPullbackMap (pullback.snd p g) (pullback.snd q g) p q g
    (pullback.fst p g) (pullback.fst q g)
    (IsPullback.of_hasPullback p g) (IsPullback.of_hasPullback q g)).isoPullback

/-- affine な標的開の制限の源は、affine な底変換射の下で affine。 -/
theorem isAffine_restrictedSource_of_baseChangeAffine (p : X ⟶ S) (q : V ⟶ S) (g : T ⟶ S)
    [IsAffine V] [IsAffineHom g] [IsAffineHom (pullback.snd p g)] :
    IsAffine (pullback (pullback.fst p q ≫ p) g) := by
  letI : IsAffine (pullback q g) := inferInstance
  letI : IsAffine (pullback (pullback.snd p g) (pullback.snd q g)) := inferInstance
  exact isAffine_of_isAffineHom (baseChangePairIso p q g).inv

end SerrePositivity.AlgebraicGeometry

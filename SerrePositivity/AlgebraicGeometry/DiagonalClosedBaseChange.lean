module

public import SerrePositivity.AlgebraicGeometry.CartesianDiagonalComparison
public import SerrePositivity.AlgebraicGeometry.ClosedPullbackComposite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：対角の実際の底変換の閉埋め込み性と、Cartesian な模型の分離性を照合する。
方針：二重交叉の比較同型と対角の Cartesian 正方形に、閉埋め込み性の移送を使う。
規約：基底の Noether 性や忠実平坦性は仮定しない。
使われ方：Stacks 01ZQ の分離性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X Y S T : Scheme.{u}} (a : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (h : IsPullback a p f g)

/-- Cartesian な模型が分離的なら、元の対角の二重交叉への実際の底変換は閉埋め込み。 -/
theorem isClosedImmersion_diagonal_pullback_of_isSeparated [IsSeparated p] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (cartesianPullbackMap p p f f g a a h h)) := by
  let sq := (isPullback_diagonal_cartesianPullbackMap a p f g h).flip
  have H : IsClosedImmersion (sq.isoPullback.inv ≫ pullback.diagonal p) := inferInstance
  simpa only [IsPullback.isoPullback_inv_snd] using H

include a h in
/-- 二重交叉の実際の模型への対角の底変換が閉埋め込みなら、Cartesian な模型は分離的。 -/
theorem isSeparated_of_closed_diagonal_stage
    [IsClosedImmersion (pullback.fst
      (pullback.snd g (pullback.fst f f ≫ f) ≫ 𝟙 _)
      (pullback.diagonal f))] : IsSeparated p := by
  let r := pullback.fst f f ≫ f
  let b := cartesianPullbackMap p p f f g a a h h
  let sq := isPullback_cartesianPullbackMap p p f f g a a h h
  let e := sq.isoPullback ≪≫ pullbackSymmetry r g
  let β := pullback.snd g r ≫ 𝟙 _
  haveI : IsClosedImmersion (pullback.snd (pullback.diagonal f) β) := by
    have H : IsClosedImmersion ((pullbackSymmetry (pullback.diagonal f) β).hom ≫
        pullback.fst β (pullback.diagonal f)) := inferInstance
    simpa using H
  have he : e.hom ≫ β = b := by
    simp [e, β, b, r, Category.assoc]
  haveI : IsClosedImmersion (pullback.snd (pullback.diagonal f) b) :=
    isClosedImmersion_pullback_snd_of_composite (pullback.diagonal f) β e.hom b he
  let hd := (isPullback_diagonal_cartesianPullbackMap a p f g h).flip
  have H : IsClosedImmersion (hd.isoPullback.hom ≫
      pullback.snd (pullback.diagonal f) b) := inferInstance
  exact ⟨by simpa only [b, IsPullback.isoPullback_hom_snd] using H⟩

end SerrePositivity.AlgebraicGeometry

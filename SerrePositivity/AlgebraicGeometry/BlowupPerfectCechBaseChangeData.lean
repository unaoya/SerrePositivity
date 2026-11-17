module

public import SerrePositivity.AlgebraicGeometry.BlowupAffineProjectiveModel
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelBaseChange
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway

/-!
概要：同じブローアップの各アフィン試験基底への表示のデータ。
方針：中心の商環表示、次数一射影表示、中心外の同型を一つにまとめる。
規約：任意の底変換が別のブローアップになるとは主張しない。
使われ方：ブローアップの普遍Čech降下性（承認済み計画I01）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- 同じ実際のpullbackの中心表示と射影表示。 -/
structure BlowupPerfectCechBaseChangeData
    {Y : Scheme.{u}} (J : Y.IdealSheafData)
    {A : Type u} [CommRing A] (t : Spec (CommRingCat.of A) ⟶ Y) where
  ideal : Ideal A
  centerIso : (J.comap t).subscheme ≅ Spec (CommRingCat.of (A ⧸ ideal ^ 1))
  center_over : centerIso.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal ^ 1))) =
    (J.comap t).subschemeι
  model : DegreeOneProjectiveModel (R := A) (pullback.snd (blowupπ J) t)
  outside : IsIso (pullback.snd (blowupπ J) t ∣_ affineCenterComplement ideal)

end SerrePositivity.AlgebraicGeometry

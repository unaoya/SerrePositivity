module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof

/-!
概要：非正次数の実三角形付き逆を、同じ実 roof の元の値の両三角形へ送る。
方針：実左細分の全射準同型の像を消去し、元の右経路の像を使う。
規約：非正次数化後に値の逆を選び直さない。使われ方：高次底変更と実不変量値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R f i m hi)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma NonpositiveInverseRoof.triangles [Epi (L.map c.sourceProjection)]
    [Epi (L.map c.roof.denominator)] (v : L.obj (Y.obj m) ⟶ L.obj (X.obj i))
    (hd : L.map c.roof.denominator ≫ v = L.map c.roof.numerator)
    (hp : L.map (c.roof.numerator ≫ f.app i) =
      L.map (c.roof.denominator ≫ Y.transition hi)) :
    L.map (f.app m) ≫ v = L.map (X.transition hi) ∧
      v ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have hden := congrArg L.map c.source_denominator
  simp only [L.map_comp] at hden
  constructor
  · apply (cancel_epi (L.map c.sourceProjection)).1
    rw [← Category.assoc, ← hden, Category.assoc, hd, ← L.map_comp,
      c.source_numerator, L.map_comp]
  · apply (cancel_epi (L.map c.roof.denominator)).1
    rw [← Category.assoc, hd, ← L.map_comp, hp, L.map_comp]

lemma NonpositiveInverseRoof.value_triangles (hL : InvertsQuasiIsos R L) :
    L.map (f.app m) ≫ c.roof.value R L hL = L.map (X.transition hi) ∧
      c.roof.value R L hL ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have := hL _ c.sourceProjection_quasiIso
  have := hL _ c.roof.denominator_quasiIso
  exact c.triangles R L _ (SurjectiveRoof.denominator_value R L hL c.roof)
    (c.rightPath.map_eq R L hL)

lemma NonpositiveInverseRoof.connectiveValue_triangles
    (hL : InvertsConnectiveQuasiIsos R L) (hX : IsConnective R (X.obj m))
    (hY : IsConnective R (Y.obj m)) (hYi : IsConnective R (Y.obj i)) :
    L.map (f.app m) ≫ c.roof.connectiveValue R L hL hY = L.map (X.transition hi) ∧
      c.roof.connectiveValue R L hL hY ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have hx : IsConnective R c.source := by
    have := c.source_nonpositive
    change c.source.X.IsLE 0
    infer_instance
  have := hL hx hX _ c.sourceProjection_quasiIso
  have := hL (c.roof.apex_isConnective R hY) hY _ c.roof.denominator_quasiIso
  exact c.triangles R L _ (SurjectiveRoof.denominator_connectiveValue R L hL hY c.roof)
    (c.rightPath.map_eq_of_connective R L hL hYi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

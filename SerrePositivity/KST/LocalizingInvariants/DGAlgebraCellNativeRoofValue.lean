module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeProRoof

/-!
概要：実三角形付き roof の逆から、同じ roof の評価で元の pro 三角形を証明する。
方針：元の左 cell augmentation を消去し、元の右乗法的経路の像を使う。
規約：同じ実 span を評価する。使われ方：具体的 IsKConnective 不変量値への接続。
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
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : CellNativeInverseRoof R f i m hi)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma CellNativeInverseRoof.triangles
    [Epi (L.map (iteratedCellAugmentation R (X.obj m) c.sourceDepth))]
    [Epi (L.map c.roof.denominator)] (v : L.obj (Y.obj m) ⟶ L.obj (X.obj i))
    (hd : L.map c.roof.denominator ≫ v = L.map c.roof.numerator)
    (hp : L.map (c.roof.numerator ≫ f.app i) =
      L.map (c.roof.denominator ≫ Y.transition hi)) :
    L.map (f.app m) ≫ v = L.map (X.transition hi) ∧
      v ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have hden := congrArg L.map c.source_denominator
  have hnum := congrArg L.map c.source_numerator
  simp only [L.map_comp] at hden hnum
  constructor
  · apply (cancel_epi (L.map (iteratedCellAugmentation R (X.obj m) c.sourceDepth))).1
    rw [← Category.assoc, ← hden, Category.assoc, hd, ← L.map_comp,
      c.source_numerator, L.map_comp]
  · apply (cancel_epi (L.map c.roof.denominator)).1
    rw [← Category.assoc, hd, ← L.map_comp, hp, L.map_comp]

lemma CellNativeInverseRoof.value_triangles (hL : InvertsQuasiIsos R L) :
    L.map (f.app m) ≫ c.roof.value R L hL = L.map (X.transition hi) ∧
      c.roof.value R L hL ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have := hL _ (iteratedCellAugmentation_quasiIso R (X.obj m) c.sourceDepth)
  have := hL _ c.roof.denominator_quasiIso
  exact c.triangles R L _ (SurjectiveRoof.denominator_value R L hL c.roof)
    (c.rightPath.map_eq R L hL)

lemma CellNativeInverseRoof.connectiveValue_triangles
    (hL : InvertsConnectiveQuasiIsos R L) (hX : IsConnective R (X.obj m))
    (hY : IsConnective R (Y.obj m)) (hYi : IsConnective R (Y.obj i)) :
    L.map (f.app m) ≫ c.roof.connectiveValue R L hL hY = L.map (X.transition hi) ∧
      c.roof.connectiveValue R L hL hY ≫ L.map (f.app i) = L.map (Y.transition hi) := by
  have he := iteratedCellAugmentation_quasiIso R (X.obj m) c.sourceDepth
  have hx := (quasiIso_isConnective_iff R _ he).2 hX
  have := hL hx hX _ he
  have := hL (c.roof.apex_isConnective R hY) hY _ c.roof.denominator_quasiIso
  exact c.triangles R L _ (SurjectiveRoof.denominator_connectiveValue R L hL hY c.roof)
    (c.rightPath.map_eq_of_connective R L hL hYi)

lemma HasCellNativeRoofProInverse.roofProInverse (h : HasCellNativeRoofProInverse R f) :
    HasSurjectiveRoofProInverse R (D := D) f := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := h i
  exact ⟨m, hi, c.roof, fun L hL => c.value_triangles R L hL⟩

lemma HasCellNativeRoofProInverse.connectiveRoofProInverse
    (h : HasCellNativeRoofProInverse R f)
    (hX : ∀ i, IsConnective R (X.obj i)) (hY : ∀ i, IsConnective R (Y.obj i)) :
    HasConnectiveRoofProInverse R (D := D) f hY := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := h i
  exact ⟨m, hi, c.roof, fun L hL => c.connectiveValue_triangles R L hL (hX m) (hY m) (hY i)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

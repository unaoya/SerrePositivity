module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementUniversalComponents

/-!
概要：有限部分集合で選んだ同じ単体列の最上位普遍 cochain を構成する。
方針：昇順列挙で元の列を制限し、元の全再添字成分式で同じ像を回収する。
規約：選択した部分集合と終端の実 frame 射を保持する。
使われ方：大域 cone/prism の始点を含む実高次成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev normalizedTensorElementSelection {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) : ⦋J.card - 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom (J.orderEmbOfFin
    (show J.card = J.card - 1 + 1 by have := Finset.card_pos.mpr hJ; omega)).toOrderHom

def normalizedTensorElementSelectedCochain {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A X ((normalizedTensorElementDiagram A X Y).obj
      (c.obj ((normalizedTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1))))) k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component (normalizedTensorElementUniversalLinear A X Y
    ((SimplexCategory.toCat.map (normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)).val
      Finset.univ k Finset.univ_nonempty (by
        have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
        simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk)

lemma normalizedTensorElementSelectedCochain_image {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last
        ((normalizedTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)))))))).f k
      (normalizedTensorElementSelectedCochain A X Y c J k hJ hk) =
    (normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk := by
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hd : k = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk
  have h := normalizedTensorElementUniversalLinear_component_inj A X Y c
    (normalizedTensorElementSelection J hJ) Finset.univ k Finset.univ_nonempty hd
    (J.orderEmbOfFin hc).injective.injOn
  have hi : (Finset.univ : Finset (Fin (J.card - 1 + 1))).image
      (normalizedTensorElementSelection J hJ).toOrderHom = J :=
    J.image_orderEmbOfFin_univ hc
  simpa only [normalizedTensorElementSelectedCochain, hi] using h

lemma normalizedTensorElementSelection_last {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) :
    (normalizedTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)) = J.max' hJ := by
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  exact Finset.orderEmbOfFin_last hc (by omega)

def normalizedTensorElementSelectedCochainAtMax {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ))) k :=
  cast (by rw [normalizedTensorElementSelection_last])
    (normalizedTensorElementSelectedCochain A X Y c J k hJ hk)

end SerrePositivity.EInfinity.ComplexLimits

module

public import SerrePositivity.InfinityCategories.F1.Coherent.PrismCutDiagonalMaximum
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.RightIntervalCutHom

/-!
概要：coherent 合成単体を同じ時刻切断で制限した実際の対角図式。
方針：元の合成単体を制限し、零時刻と一時刻の対象を正規化する。
規約：二つの元の豊穣 Hom の同時パラメーターを保つ。
使われ方：合成三角形の対角を元の豊穣合成の標準 Hom 比較と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
variable (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
variable (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)

/-- 同じ時刻ラベルで合成単体を制限した、元の対角の coherent 図式。 -/
def coherentCompositionDiagonalCutSimplex : (SimplicialNerve C) _⦋n⦌ :=
  (SimplicialNerve C).map (SimplexCategory.mkHom (coherentPrismCut t)).op
    (coherentCompositionSimplex σ τ t)

/-- 同じ対角図式の零時刻の対象は、元の始域対象。 -/
lemma coherentCompositionDiagonalCutSimplex_obj_zero
    (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentCompositionDiagonalCutSimplex σ τ t).obj ⟨ULift.up i⟩ = X := by
  change coherentCompositionObj X Y Z t (coherentPrismCut t i) = X
  rw [coherentPrismCut_zero t i hi, coherentCompositionObj_zero X Y Z t i hi]

/-- 同じ対角図式の一時刻の対象は、元の最終対象。 -/
lemma coherentCompositionDiagonalCutSimplex_obj_one
    (i : Fin (n + 1)) (hi : t i = 1) :
    (coherentCompositionDiagonalCutSimplex σ τ t).obj ⟨ULift.up i⟩ = Z := by
  change coherentCompositionObj X Y Z t (coherentPrismCut t i) = Z
  rw [coherentPrismCut_one t i (by rw [hi]; decide), coherentCompositionObj_last]

/-- 同じ対角図式の零時刻内の Hom は元の始域の恒等に定値。 -/
lemma coherentCompositionDiagonalCutSimplex_zeroHom
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    (coherentCompositionDiagonalCutSimplex σ τ t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi)
        (coherentCompositionDiagonalCutSimplex_obj_zero σ τ t j hj)) = toUnit _ ≫ eId SSet X := by
  change (_ ≫ coherentCompositionHom σ τ t (coherentPrismCut t i)
    (coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentCompositionHom_transport σ τ t
    (coherentPrismCut_zero t i hi) (coherentPrismCut_zero t j hj)
    (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_zero X Y Z t j hj),
    coherentCompositionHom_zero_zero σ τ t i j hi hj]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

/-- 同じ対角図式の一時刻内の Hom は元の最終対象の恒等に定値。 -/
lemma coherentCompositionDiagonalCutSimplex_oneHom
    (i j : Fin (n + 1)) (hi : t i = 1) (hj : t j = 1) :
    (coherentCompositionDiagonalCutSimplex σ τ t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionDiagonalCutSimplex_obj_one σ τ t i hi)
        (coherentCompositionDiagonalCutSimplex_obj_one σ τ t j hj)) = toUnit _ ≫ eId SSet Z := by
  change (_ ≫ coherentCompositionHom σ τ t (coherentPrismCut t i)
    (coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentCompositionHom_transport σ τ t
    (coherentPrismCut_one t i (by rw [hi]; decide))
    (coherentPrismCut_one t j (by rw [hj]; decide))
    (coherentCompositionObj_last X Y Z n t) (coherentCompositionObj_last X Y Z n t),
    coherentCompositionHom_last_last]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories

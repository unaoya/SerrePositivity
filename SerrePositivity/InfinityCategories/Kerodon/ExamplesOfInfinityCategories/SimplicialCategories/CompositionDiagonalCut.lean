module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismCutDiagonalMaximum
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.RightIntervalCutHom

/-!
概要：coherent 合成単体を同じ時刻切断で制限した実際の対角図式。
方針：元の合成単体を制限し、零時刻と一時刻の対象を正規化する。
規約：二つの元の豊穣 Hom の同時パラメーターを保つ。
使われ方：合成三角形の対角を元の豊穣合成の標準 Hom 比較と照合する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
variable (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
variable (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)

/-- 同じ時刻ラベルで合成単体を制限した、元の対角の coherent 図式。 -/
def coherentCompositionDiagonalCutSimplex : (SimplicialNerve C) _⦋n⦌ :=
  (SimplicialNerve C).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t)).op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex σ τ t)

/-- 同じ対角図式の零時刻の対象は、元の始域対象。 -/
lemma coherentCompositionDiagonalCutSimplex_obj_zero
    (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentCompositionDiagonalCutSimplex σ τ t).obj ⟨ULift.up i⟩ = X := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i) = X
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t i hi]

/-- 同じ対角図式の一時刻の対象は、元の最終対象。 -/
lemma coherentCompositionDiagonalCutSimplex_obj_one
    (i : Fin (n + 1)) (hi : t i = 1) :
    (coherentCompositionDiagonalCutSimplex σ τ t).obj ⟨ULift.up i⟩ = Z := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i) = Z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t i (by rw [hi]; decide), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last]

/-- 同じ対角図式の零時刻内の Hom は元の始域の恒等に定値。 -/
lemma coherentCompositionDiagonalCutSimplex_zeroHom
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    (coherentCompositionDiagonalCutSimplex σ τ t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi)
        (coherentCompositionDiagonalCutSimplex_obj_zero σ τ t j hj)) = toUnit _ ≫ eId SSet X := by
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_transport σ τ t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t j hj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z t j hj),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ t i j hi hj]
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
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_transport σ τ t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t i (by rw [hi]; decide))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t j (by rw [hj]; decide))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n t),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

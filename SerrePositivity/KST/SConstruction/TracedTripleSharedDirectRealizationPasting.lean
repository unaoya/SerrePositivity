module
public import SerrePositivity.KST.SConstruction.TracedTripleSharedDirectPasting

/-! # 元の共有直接補正の全高次比較と両正規化円柱を同じ実複体へ保つ
概要：共有直接比較円柱を既存面として、元の全高次比較と両元の正規化円柱全体を貼る。
方針：同じ全比較円柱の厳密な回収式を、比較面包含の pushout に渡す。
規約：元の十面・全円柱・全高次比較を保持し、新しい比較や面を選ばない。
使われ方：元の raw BF 二三角形を接続し、保持した実複体から第四辺比較を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet Spectra
open scoped Simplicial

/-- 元の全共有直接比較を、その同じ全円柱面で既存複体へ貼った実複体。 -/
def tripleSharedDirectRealizationPasting : SSet.{u} :=
  pushout tripleSharedDirectPastingCell.{u}
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3))

/-- 元の全十面・全円柱を持つ既存複体全体の包含。 -/
def tripleSharedDirectRealizationPastingOriginal :
    tripleSharedDirectPasting.{u} ⟶ tripleSharedDirectRealizationPasting :=
  pushout.inl tripleSharedDirectPastingCell.{u}
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3))

/-- 元の全高次直接比較の同じ包含。 -/
def tripleSharedDirectRealizationPastingCell :
    (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ tripleSharedDirectRealizationPasting :=
  pushout.inr tripleSharedDirectPastingCell.{u}
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3))

/-- 元の共有直接円柱は、実複体内で元の高次比較の同じ全指定面。 -/
lemma tripleSharedDirectRealizationPasting_shared :
    tripleSharedDirectPastingCell.{u} ≫ tripleSharedDirectRealizationPastingOriginal =
      ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3)) ≫
        tripleSharedDirectRealizationPastingCell := pushout.condition

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の十面と全正規化・直接比較・全高次比較を同時に保持する実写像。 -/
def monicKTracedTripleSharedDirectRealizationPasting (n : ℕ) :
    tripleSharedDirectRealizationPasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  pushout.desc
    (f := tripleSharedDirectPastingCell.{u})
    (g := (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3))
    (monicKTracedTripleSharedDirectPasting F f g h n)
    (monicKTracedTripleDirectComparisonRealization F f g h n)
    ((monicKTracedTripleSharedDirectPasting_cell F f g h n).trans
      (monicKTracedTripleDirectComparisonRealization_comparison F f g h n).symm)

/-- 元の十面・全円柱の複体全体を厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_original (n : ℕ) :
    tripleSharedDirectRealizationPastingOriginal ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      monicKTracedTripleSharedDirectPasting F f g h n := pushout.inl_desc _ _ _

/-- 元の全高次直接比較そのものも厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_family (n : ℕ) :
    tripleSharedDirectRealizationPastingCell ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      monicKTracedTripleDirectComparisonRealization F f g h n := pushout.inr_desc _ _ _

/-- 元の共有直接比較円柱全体を、元の高次比較の同じ全指定面として保持する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_comparison (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫ tripleSharedDirectRealizationPastingCell ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      (monicKTracedTripleDirectComparison F f g h n).h := by
  rw [monicKTracedTripleSharedDirectRealizationPasting_family]
  exact monicKTracedTripleDirectComparisonRealization_comparison F f g h n

/-- 元の左直接補正の全正規化円柱も、同じ実複体の高次比較面として保持する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_left (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ tripleSharedDirectRealizationPastingCell ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      (monicKTracedCompositionStageFirstNormalization F (f ≫ g) h n).h := by
  rw [monicKTracedTripleSharedDirectRealizationPasting_family]
  exact monicKTracedTripleDirectComparisonRealization_left F f g h n

/-- 元の右直接補正の全正規化円柱も、同じ実複体の高次比較面として保持する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_right (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫ tripleSharedDirectRealizationPastingCell ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      (monicKTracedCompositionStageFirstNormalization F f (g ≫ h) n).h := by
  rw [monicKTracedTripleSharedDirectRealizationPasting_family]
  exact monicKTracedTripleDirectComparisonRealization_right F f g h n

/-- 元の全高次比較は、同じ全入力区間境界を全パラメータで厳密に固定する。 -/
lemma monicKTracedTripleSharedDirectRealizationPasting_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫ tripleSharedDirectRealizationPastingCell ≫
        monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      CartesianMonoidalCategory.fst (∂Δ[1] : SSet.{u}) Δ[2] ≫ (SSet.boundary 1).ι ≫
        monicKTracedUnaryCorrectionAtPoint F (f ≫ g ≫ h) n := by
  rw [monicKTracedTripleSharedDirectRealizationPasting_family]
  exact monicKTracedTripleDirectComparisonRealization_relative F f g h n

end SerrePositivity.KST.SConstruction

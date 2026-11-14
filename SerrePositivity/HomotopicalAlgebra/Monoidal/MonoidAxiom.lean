module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass

/-! # The monoid axiom and tensor-cell acyclicity

The monoid axiom is extra compatibility of the existing model and monoidal
structures. It controls tensoring trivial cofibrations with arbitrary objects,
then coproducts, pushouts and transfinite compositions in the stated universe.
No cofibrancy of the tensor parameter is imposed. Retracts are handled using
weak-equivalence retract stability, rather than included as new axioms.
-/

@[expose] public section
universe w u v
open CategoryTheory HomotopicalAlgebra CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Images of P under right tensor with all objects, allowing arrow isomorphisms
as in Mathlib `MorphismProperty.map`. -/
def tensorRightImages (P : MorphismProperty C) : MorphismProperty C :=
  ⨆ X : C, P.map (tensorRight X)

lemma tensorRightImages_monotone : Monotone (tensorRightImages (C := C)) := by
  intro P Q h
  apply iSup_le
  intro X
  exact (MorphismProperty.monotone_map (tensorRight X) h).trans
    (le_iSup (fun X : C ↦ Q.map (tensorRight X)) X)

lemma tensorRight_mem {P : MorphismProperty C} {A B : C} (f : A ⟶ B) (hf : P f)
    (X : C) : tensorRightImages P (f ▷ X) :=
  (le_iSup (fun X : C ↦ P.map (tensorRight X)) X) _ (P.map_mem_map _ f hf)

/-- Braiding transports left tensor generators into the same right tensor class. -/
lemma tensorLeft_mem [BraidedCategory C] {P : MorphismProperty C}
    {A B : C} (f : A ⟶ B) (hf : P f) (X : C) : tensorRightImages P (X ◁ f) := by
  have h : (P.map (tensorRight X)) (X ◁ f) := by
    apply ((P.map (tensorRight X)).arrow_mk_iso_iff
      (Arrow.isoMk (β_ A X) (β_ B X) (BraidedCategory.braiding_naturality_left f X).symm)).1
    exact P.map_mem_map (tensorRight X) f hf
  exact (le_iSup (fun X : C ↦ P.map (tensorRight X)) X) _ h

/-- Relative cell complexes with explicit coproduct and ordinal universes. -/
abbrev relativeCells (P : MorphismProperty C) : MorphismProperty C :=
  MorphismProperty.transfiniteCompositions.{w} (MorphismProperty.coproducts.{w} P).pushouts

omit [MonoidalCategory C] in
lemma relativeCells_monotone : Monotone (relativeCells.{w} (C := C)) := by
  intro P Q h
  exact MorphismProperty.transfiniteCompositions_monotone
    (MorphismProperty.pushouts_monotone (MorphismProperty.coproducts_monotone h))

omit [MonoidalCategory C] in
lemma le_relativeCells (P : MorphismProperty C) : P ≤ relativeCells.{w} P :=
  P.le_coproducts.trans ((MorphismProperty.coproducts.{w} P).le_pushouts.trans
    ((MorphismProperty.coproducts.{w} P).pushouts.le_transfiniteCompositions))

variable (C) [ModelCategory C]

/-- Tensor-cell weak equivalence compatibility, independently of the unit and
pushout-product axioms. The universe w is part of the contract. -/
class HasMonoidAxiom : Prop where
  tensorCells : relativeCells.{w} (tensorRightImages (trivialCofibrations C)) ≤
    weakEquivalences C

variable {C}

lemma tensor_trivialCofibration_weakEquivalence [HasMonoidAxiom.{w} C]
    {A B : C} (f : A ⟶ B) [Cofibration f] [WeakEquivalence f] (X : C) :
    WeakEquivalence (f ▷ X) := by
  exact ⟨HasMonoidAxiom.tensorCells _
    (le_relativeCells _ _ (tensorRight_mem f (mem_trivialCofibrations f) X))⟩

/-- Any generating subclass of trivial cofibrations has acyclic tensor cells. -/
lemma tensorCells_le_weakEquivalences [HasMonoidAxiom.{w} C]
    (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C) :
    relativeCells.{w} (tensorRightImages J) ≤ weakEquivalences C :=
  (relativeCells_monotone (tensorRightImages_monotone hJ)).trans HasMonoidAxiom.tensorCells

/-- Retracts of these tensor-cell maps remain weak equivalences. -/
lemma tensorCells_retracts_le_weakEquivalences [HasMonoidAxiom.{w} C]
    (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C) :
    (relativeCells.{w} (tensorRightImages J)).retracts ≤ weakEquivalences C :=
  (MorphismProperty.retracts_monotone (tensorCells_le_weakEquivalences J hJ)).trans
    (weakEquivalences C).retracts_le

/-- Generated tensor left classes are acyclic when their small-object
hypothesis is supplied separately; the monoid axiom supplies no smallness. -/
lemma tensorGenerated_le_weakEquivalences [HasMonoidAxiom.{w} C]
    (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C)
    [(tensorRightImages J).HasSmallObjectArgument.{w}] :
    (tensorRightImages J).rlp.llp ≤ weakEquivalences C :=
  SerrePositivity.ModelGeneration.generatedLeft_le_of_cells_le _ _
    (tensorCells_le_weakEquivalences J hJ)

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.8.1" (partial := component) "仮定：モノイダル圏とモデル構造（Lean が弱い：組合せ的・対称であることを仮定しない）。結論：自明余ファイブレーションを右から任意の対象でテンソルして作る、指定宇宙の余積・押し出し・超限合成とそのレトラクトの弱同値性（対称な場合に HA の生成射と同じ右テンソル側）。全宇宙の最小弱飽和類との比較は型に含まれない。"] _root_.SerrePositivity.Quillen.HasMonoidAxiom
attribute [cite HA "4.1.8.1" (partial := component) "仮定：モノイダル圏とモデル構造（Lean が弱い：組合せ的・対称であることを仮定しない）。結論：自明余ファイブレーションを右から任意の対象でテンソルして作る、指定宇宙の余積・押し出し・超限合成とそのレトラクトの弱同値性（対称な場合に HA の生成射と同じ右テンソル側）。全宇宙の最小弱飽和類との比較は型に含まれない。"] _root_.SerrePositivity.Quillen.tensorCells_retracts_le_weakEquivalences
attribute [cite HA "4.5.4.2" (partial := component) "仮定：モノイダル圏とモデル構造（Lean は組合せ性と対称性を要求しない）。結論：指定宇宙のテンソル生成セルとそのレトラクトの弱同値性（F1 のモノイド公理の範囲に一致）。F2 の組と Σₙ 射影モデルでの F3 は型に含まれない。"] _root_.SerrePositivity.Quillen.HasMonoidAxiom
attribute [cite HA "4.5.4.2" (partial := component) "仮定：モノイダル圏とモデル構造（Lean は組合せ性と対称性を要求しない）。結論：指定宇宙のテンソル生成セルとそのレトラクトの弱同値性（F1 のモノイド公理の範囲に一致）。F2 の組と Σₙ 射影モデルでの F3 は型に含まれない。"] _root_.SerrePositivity.Quillen.tensorCells_retracts_le_weakEquivalences

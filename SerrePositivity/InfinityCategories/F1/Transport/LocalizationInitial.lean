module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexNerveColimit
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationPushout
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：同型が反転する辺に関する局所化と、空の底上の初頂点写像の局所化。
方針：周囲の前合成の同型を全部分複体へ制限し、初対象の保存を適用する。
規約：空の底やその単体圏を特定の表示に固定しない。
使われ方：一般の底へのセル帰納法の初期段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同型に沿う局所化の前合成は、実際の単体集合の同型。 -/
lemma isIso_localizationPrecomposition_of_isIso {A B : SSet.{u}} (F : A ⟶ B) [IsIso F]
    (W : Set (A _⦋1⦌)) (hF : InvertsEdges F W) (E : SSet.{u}) :
    IsIso (localizationPrecomposition F W hF E) := by
  let L := localizationPrecomposition F W hF E
  let J := (invertingFunctors A E W).ι
  let P := (pre F).app E
  have hLP : L ≫ J = P := localizationPrecomposition_ι F W hF E
  have : IsIso P := by
    change IsIso ((internalHom.flip.obj E).map F.op)
    infer_instance
  refine ⟨⟨J ≫ inv P, ?_, ?_⟩⟩
  · rw [← Category.assoc, hLP, IsIso.hom_inv_id]
  · apply (cancel_mono J).mp
    rw [Category.assoc, Category.assoc, hLP, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- 単体集合の同型は、その同型が実際に反転する指定辺に関して局所化を表す。 -/
lemma isLocalization_of_isIso {A B : SSet.{u}} (F : A ⟶ B) [IsIso F]
    (W : Set (A _⦋1⦌)) (hF : InvertsEdges F W) : IsLocalization F W := by
  refine ⟨hF, fun E _ ↦ ?_⟩
  have := isIso_localizationPrecomposition_of_isIso F W hF E
  exact (qCatEquivalenceOfIso (asIso (localizationPrecomposition F W hF E))).isQCatEquivalence

/-- 空の底では、単体圏からの初頂点写像は同型であり局所化を表す。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_isInitial {B : SSet.{u}}
    (hB : IsInitial B) :
    IsLocalization (transportSimplexFirstVertexMap B) (transportSimplexInitialEdges B) := by
  have hT : IsInitial (nerve (TransportSimplexCategory B)) :=
    hB.isInitialObj transportSimplexNerveFunctor
  have : IsIso (transportSimplexFirstVertexMap B) := isIso_of_isInitial hT hB _
  exact isLocalization_of_isIso (transportSimplexFirstVertexMap B)
    (transportSimplexInitialEdges B) (transportSimplexFirstVertexMap_inverts B)

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.KST.Spectra.OverChainCoproduct
public import SerrePositivity.KST.Spectra.LatchingCoproductMono
public import SerrePositivity.KST.Spectra.StandardSimplexLatching
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：余単体圏上の BK 重みの実際の latching 射は単射。
方針：各単体次数を representable の余積へ分解し、標準単体の latching の単射性を移す。
規約：AsSmall 上の BK 重みを元の余単体圏へ制限する。
使われ方：Goerss–Jardine VII §4。通常 Tot 比較に必要な重みの Reedy cofibrancy。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.BousfieldKanWeightLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 単体次数で評価した latching と元の latching の評価との arrow 同型。 -/
def evaluationArrowIso (F : CosimplicialObject SSet.{u})
    (k : SimplexCategoryᵒᵖ) (j : SimplexCategory) :
    Arrow.mk ((latchingComparison simplex j).app
      (F ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj k)) ≅
    Arrow.mk (((latchingComparison simplex j).app F).app k) :=
  Arrow.isoMk
    (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type u)).obj k)
      (latchingSource simplex j ⋙ F)).symm (Iso.refl _) (by
        change (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type u)).obj k)
          (latchingSource simplex j ⋙ F)).inv ≫
          ((latchingComparison simplex j).app F).app k = _ ≫ 𝟙 _
        rw [Category.comp_id]
        change (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type u)).obj k)
          (latchingSource simplex j ⋙ F)).inv ≫
          ((evaluation SimplexCategoryᵒᵖ (Type u)).obj k).map
            (colimit.desc _ (latchingCocone simplex F j)) = _
        rw [preservesColimitIso_inv_comp_desc]
        rfl)

/-- AsSmall 上の representable を元の余単体圏へ制限した図式の latching は単射。 -/
lemma representable_mono (n : ℕ)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) (j : SimplexCategory) :
    Mono ((latchingComparison simplex j).app
      (AsSmall.up ⋙
        OverChainCoordinates.representableFamily (AsSmall.{u} SimplexCategory) n σ)) := by
  let k := Opposite.op (AsSmall.down.obj (σ.obj (Fin.last n)))
  let : Mono ((latchingComparison simplex j).app stdSimplex.{u}) :=
    StandardSimplexLatching.mono j
  have h : Mono (((latchingComparison simplex j).app stdSimplex.{u}).app k) := inferInstance
  exact ((MorphismProperty.monomorphisms (Type u)).arrow_iso_iff
    (evaluationArrowIso stdSimplex.{u} k j)).mpr h

/-- representable の余積表示を制限した座標図式でも latching は単射。 -/
lemma coordinates_mono (n : ℕ) (j : SimplexCategory) :
    Mono ((latchingComparison simplex j).app
      (AsSmall.up ⋙ OverChainCoordinates.coordinateDiagram (AsSmall.{u} SimplexCategory) n)) := by
  let P := (Functor.whiskeringLeft SimplexCategory (AsSmall.{u} SimplexCategory) (Type u)).obj
    AsSmall.up
  let F := fun σ : ComposableArrows (AsSmall.{u} SimplexCategory) n ↦
    AsSmall.up ⋙ OverChainCoordinates.representableFamily (AsSmall.{u} SimplexCategory) n σ
  let e := Discrete.compNatIsoDiscrete
    (OverChainCoordinates.representableFamily (AsSmall.{u} SimplexCategory) n) P
  let c : Cofan F := (Cocone.precompose e.inv).obj
    (P.mapCocone (OverChainCoordinates.coordinateCofan (AsSmall.{u} SimplexCategory) n))
  have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm
    (isColimitOfPreserves P
      (OverChainCoordinates.coordinateCofanIsColimit (AsSmall.{u} SimplexCategory) n))
  exact LatchingCoproductMono.of_cofan simplex F c hc j (fun σ ↦ representable_mono n σ j)

/-- 元の余単体圏へ制限した実際の BK 重み。 -/
abbrev weight : CosimplicialObject SSet.{u} :=
  AsSmall.up ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} SimplexCategory)

/-- 各単体次数の BK 重みの latching は単射。 -/
lemma degree_mono (n : ℕ) (j : SimplexCategory) :
    Mono ((latchingComparison simplex j).app
      (weight.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌))) := by
  let e := Functor.isoWhiskerLeft AsSmall.up
    (OverChainCoordinates.degreeIso (AsSmall.{u} SimplexCategory) n)
  let a : Arrow.mk ((latchingComparison simplex j).app
      (weight.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌))) ≅
      Arrow.mk ((latchingComparison simplex j).app
        (AsSmall.up ⋙ OverChainCoordinates.coordinateDiagram (AsSmall.{u} SimplexCategory) n)) :=
    Arrow.isoMk ((latchingEvaluation simplex j).mapIso e)
      (e.app j) ((latchingComparison simplex j).naturality e.hom)
  exact ((MorphismProperty.monomorphisms (Type u)).arrow_iso_iff a).mpr (coordinates_mono n j)

/-- BK 重みの全ての latching 射は単射。 -/
lemma mono (j : SimplexCategory) : Mono ((latchingComparison simplex j).app weight.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  have h := degree_mono.{u} k.unop.len j
  exact ((MorphismProperty.monomorphisms (Type u)).arrow_iso_iff
    (evaluationArrowIso weight.{u} k j)).mp h

/-- 空な図式からの相対 latching 射と通常の latching 射のモデル圏非依存の同型。 -/
def initialArrowIso (F : CosimplicialObject SSet.{u}) (j : SimplexCategory) :
    Arrow.mk ((latchingComparison simplex j).app F) ≅
      Arrow.mk (relativeLatchingMap simplex j (initial.to F)) := by
  let : IsIso ((latchingComparison simplex j).app (⊥_ (SimplexCategory ⥤ SSet.{u}))) :=
    isIso_of_isInitial
      (initialIsInitial.isInitialObj (latchingEvaluation simplex j) _)
      (initialIsInitial.isInitialObj ((evaluation SimplexCategory SSet.{u}).obj j) _) _
  exact Arrow.isoMk
    (asIso (pushout.inl ((latchingEvaluation simplex j).map (initial.to F))
      ((latchingComparison simplex j).app (⊥_ (SimplexCategory ⥤ SSet.{u})))))
    (Iso.refl _) ((inl_relativeLatchingMap simplex j (initial.to F)).trans
      (Category.comp_id ((latchingComparison simplex j).app F)).symm)

/-- BK 重みは単射を左類とする実際の Reedy cofibrant 図式。 -/
lemma reedyCofibrant :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (initial.to weight.{u}) := by
  intro j
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
    (initialArrowIso weight.{u} j)).mp (mono j)

end
end SerrePositivity.KST.Spectra.BousfieldKanWeightLatching

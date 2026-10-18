module

public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap
public import SerrePositivity.KST.Spectra.EndLimitPreservation
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：点つき重み付き end は重みの余極限を通常の極限へ送る。
方針：自由基点の随伴、反変な内部 Hom の極限保存、end の極限保存を合成する。
規約：重みについて反変。ホモトピー極限性や π_* の交換は主張しない。
使われ方：Goerss–Jardine VIII §1。有限骨格の end の塔の厳密な極限。
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet Opposite

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightLimitsPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：重みから end の二変数図式への反変関手。
方針：自由基点と反対関手を通じて enriched Hom の図式を関手化する。
規約：end を取る前の図式全体を値とする。
使われ方：Goerss–Jardine VIII §1。極限の成分ごとの検査。 -/
def weightDiagramFunctor (D : I ⥤ PointedSimplicialSet.{u}) :
    (I ⥤ SSet.{u})ᵒᵖ ⥤ Iᵒᵖ ⥤ I ⥤ PointedSimplicialSet.{u} :=
  ((Functor.whiskeringRight I SSet.{u} PointedSimplicialSet.{u}).obj
      PointedObject.adjoinFunctor).op ⋙
    (Functor.opUnopEquiv I PointedSimplicialSet.{u}).functor ⋙
    (Functor.whiskeringRight Iᵒᵖ PointedSimplicialSet.{u}ᵒᵖ
      (I ⥤ PointedSimplicialSet.{u})).obj
        (eHomFunctor PointedSimplicialSet.{u} PointedSimplicialSet.{u} ⋙
          (Functor.whiskeringLeft I PointedSimplicialSet.{u} PointedSimplicialSet.{u}).obj D)

/-- 概要：end の図式の固定成分は反変な内部 Hom の合成で表示できる。
方針：自己豊穣構造の右前合成と閉構造の pre の一致を使う。
規約：i は反変な添字、j は係数の添字。
使われ方：Goerss–Jardine VIII §1。成分の極限保存の検査。 -/
def weightEvaluationIso (D : I ⥤ PointedSimplicialSet.{u}) (i j : I) :
    weightDiagramFunctor D ⋙
      ((evaluation Iᵒᵖ (I ⥤ PointedSimplicialSet.{u})).obj (op i) ⋙
        (evaluation I PointedSimplicialSet.{u}).obj j) ≅
    ((evaluation I SSet.{u}).obj i).op ⋙ PointedObject.adjoinFunctor.op ⋙
      internalHom.flip.obj (D.obj j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    change eHomWhiskerRight PointedSimplicialSet.{u}
        (PointedObject.adjoinFunctor.map (f.unop.app i)) (D.obj j) ≫ 𝟙 _ =
      𝟙 _ ≫ (pre (PointedObject.adjoinFunctor.map (f.unop.app i))).app (D.obj j)
    rw [Category.comp_id, Category.id_comp, enrichedOrdinaryCategorySelf_eHomWhiskerRight])

instance weightDiagramFunctor_preservesLimitsOfShape
    (D : I ⥤ PointedSimplicialSet.{u}) (K : Type v) [Category.{w} K]
    [HasColimitsOfShape Kᵒᵖ SSet.{u}] :
    PreservesLimitsOfShape K (weightDiagramFunctor D) := by
  apply preservesLimitsOfShape_of_evaluation
  intro i
  apply preservesLimitsOfShape_of_evaluation
  intro j
  let := (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).isLeftAdjoint
  let := preservesLimitsOfShape_op K ((evaluation I SSet.{u}).obj i.unop)
  let := preservesLimitsOfShape_op K (PointedObject.adjoinFunctor (C := SSet.{u}))
  exact preservesLimitsOfShape_of_natIso (weightEvaluationIso D i.unop j).symm

/-- 概要：点つき end の重み関手を図式関手と end 関手の合成として表示する。
方針：成分を恒等同型とし、end の各射影で前合成の一致を示す。
規約：同型は実際の重みの前合成に自然。
使われ方：Goerss–Jardine VIII §1。重みの余極限からの極限保存の合成。 -/
def weightFunctorEndIso (D : I ⥤ PointedSimplicialSet.{u}) :
    weightFunctor D ≅ weightDiagramFunctor D ⋙ endFunctor I PointedSimplicialSet.{u} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    change preMap f.unop D ≫ 𝟙 _ = 𝟙 _ ≫ end_.map _
    rw [Category.comp_id, Category.id_comp]
    apply end_.hom_ext
    intro i
    rw [preMap_π, end_.map_π]
    change _ ≫ (pre (PointedObject.adjoinFunctor.map (f.unop.app i))).app (D.obj i) =
      _ ≫ eHomWhiskerRight PointedSimplicialSet.{u}
        (PointedObject.adjoinFunctor.map (f.unop.app i)) (D.obj i)
    rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight])

instance weightFunctor_preservesLimit (D : I ⥤ PointedSimplicialSet.{u})
    {K : Type v} [Category.{w} K] [HasColimitsOfShape Kᵒᵖ SSet.{u}]
    [HasLimitsOfShape K PointedSimplicialSet.{u}] (F : K ⥤ (I ⥤ SSet.{u})ᵒᵖ) :
    PreservesLimit F (weightFunctor D) := by
  exact preservesLimit_of_natIso F (weightFunctorEndIso D).symm

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd

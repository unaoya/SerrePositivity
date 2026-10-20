module

public import SerrePositivity.EInfinity.ComplexLimits.WeightedCotensor
public import SerrePositivity.EInfinity.HomotopyWeight.PointReplacement
public import SerrePositivity.EInfinity.HomotopyWeight.Reindex
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
# Cofibrant な一点重みの右 frame の end の関手

概要：Hovey §5.4 の一般 homotopy 極限の計算対象を小図式全体に関手的に構成する。
方針：関手的右 frame と実際の Yoneda の左 Kan 拡張を指定した重みで評価する。
規約：対象と射を構成する。ホモトピー不変性・右導来極限の普遍性は別に証明する。
使われ方：E2a-4 の一般 homotopy 極限の計算モデル。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：選んだ一点重みを右 frame の反対添字へ移す（Hovey §5.4）。
方針：二重反対圏の同値に沿う前合成を使う。
規約：実際の射影 cofibrant な一点重みそのものを使う。
使われ方：重み付き end を図式全体の関手として評価する。 -/
abbrev framedLimitWeight := (doubleOpWeights K).obj (HomotopyWeight.weight K)

/-- 概要：元の小図式を反対圏の右 frame の図式へ関手的に移す（Hovey §5.2）。
方針：図式圏の反対化と関手的右 frame の後合成を使う。
規約：図式射の合成を厳密に保つ。
使われ方：重み付き実現の係数に関する自然性。 -/
def rightFrameDiagramFamily :
    (K ⥤ (Complex A))ᵒᵖ ⥤ Kᵒᵖ ⥤ SimplexCategory ⥤ (Complex A)ᵒᵖ := by
  let := projectiveModelCategory A
  exact (Functor.opUnopEquiv K (Complex A)).functor ⋙
    (Functor.whiskeringRight Kᵒᵖ _ _).obj (rightFrameFamily A).obj

/-- 概要：反対圏での重み付き右 frame の end の関手（Hovey §5.4）。
方針：図式の反対化・右 frame・随伴で自然な重み付き実現・重みでの評価を合成する。
規約：すべての操作は厳密な関手で、各対象ごとの選択から自然性を仮定しない。
使われ方：元の 複体圏に値を取る計算関手の構成。 -/
def framedLimitOpFunctor : (K ⥤ (Complex A))ᵒᵖ ⥤ (Complex A)ᵒᵖ := by
  exact rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ ⋙
    (CategoryTheory.evaluation _ (Complex A)ᵒᵖ).obj (framedLimitWeight K)

/-- 概要：小図式の射影 cofibrant な一点重みの右 frame の end の関手（Hovey §5.4）。
方針：反対圏で構成した関手を unop する。
規約：任意の小図式と全図式射、単体集合のモデル存在の仮定なし。
使われ方：一般 homotopy 極限の導来普遍性を証明する元の計算関手。 -/
def framedLimitFunctor : (K ⥤ (Complex A)) ⥤ (Complex A) :=
  (framedLimitOpFunctor A K).unop

/-- 概要：計算関手の各値は選んだ重みの実際の右 frame の end（Hovey §5.4）。
方針：合成関手の対象の式を評価する。
規約：重みや frame の置換を選び直さない。
使われ方：構成済みの重み付き Hom と底の比較を計算関手へ移す。 -/
lemma framedLimitFunctor_obj (F : K ⥤ (Complex A)) :
    (framedLimitFunctor A K).obj F =
      (weightedCotensor A K F).obj (op (HomotopyWeight.weight K)) := rfl


/-- 概要：計算対象の二重反対化した一点重みは射影 cofibrant（Hovey §5.4）。
方針：添字の同値による保存と初期図式の同型を使う。
規約：元の自由境界の左類を保持する。
使われ方：一般 homotopy 極限の実現と写像空間の不変性。 -/
lemma framedLimitWeight_cofibrant :
    (HomotopyWeight.boundaries Kᵒᵖᵒᵖ).rlp.llp (initial.to (framedLimitWeight K)) := by
  have h := HomotopyWeight.reindex_cofibration (opOpEquivalence K)
    (initial.to (HomotopyWeight.weight K)) (HomotopyWeight.weight_cofibrant K)
  let hi := initialIsInitial.isInitialObj (doubleOpWeights K) (⊥_ K ⥤ SSet.{u})
  let e : (doubleOpWeights K).obj (⊥_ K ⥤ SSet.{u}) ≅ (⊥_ Kᵒᵖᵒᵖ ⥤ SSet.{u}) :=
    hi.uniqueUpToIso initialIsInitial
  let a : Arrow.mk ((doubleOpWeights K).map (initial.to (HomotopyWeight.weight K))) ≅
      Arrow.mk (initial.to (framedLimitWeight K)) :=
    Arrow.isoMk e (Iso.refl _) (hi.hom_ext _ _)
  exact ((HomotopyWeight.boundaries Kᵒᵖᵒᵖ).rlp.llp.arrow_mk_iso_iff a).mp h


end SerrePositivity.EInfinity.ComplexLimits

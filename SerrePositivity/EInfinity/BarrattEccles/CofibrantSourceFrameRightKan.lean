module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameLimits
public import SerrePositivity.EInfinity.FrameHom.FrameRightKan
public import SerrePositivity.EInfinity.FrameHom.FrameArrowRightKan

/-!
# 元の cofibrant source frame から実 hammock の右 Kan 形状への比較

概要：同じ augmentation・同じ qX を用い、次数圏と全矢圏の二つの実比較を供給する。
方針：元の弱同値反転を全 coslice prism の実現へ代入する。
規約：元の始域射影と全 rightKanDiagram の制限を厳密に保持する。
使われ方：CAlg_R の局所化普遍性の実右 Kan 比較。cofinal 性は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SerrePositivity.InfinityCategories
open SimplicialLocalization FrameHom.FrameArrows
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CofibrantAlgebra A)

def cofibrantHammockVertex :
    (kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌ :=
  (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
    (nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from X))

lemma cofibrantSourceFrameAugmentation_invertible (n : AsSmall.{u + 1} SimplexCategory) :
    IsInvertibleEdge ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))).toTruncated := by
  have hw := hammockLocalizationNerveMap_inverts (cofibrantAlgebraRelativeCategory A)
    (show ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n) ∈
        weakNerveEdges (cofibrantAlgebraRelativeCategory A) from
      ⟨_, _, _, cofibrantDKSourceFrameAugmentation_weak A X n, rfl⟩)
  change IsInvertibleEdge (X := kanHammockNerve (cofibrantAlgebraRelativeCategory A))
    ((edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
      ((SSet.truncation 2).map
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)))) at hw
  exact (isInvertibleEdge_congr
    (X := kanHammockNerve (cofibrantAlgebraRelativeCategory A)) (e :=
    (edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
      ((SSet.truncation 2).map
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))))
    (f := ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))).toTruncated) rfl).mp hw

def cofibrantSourceFrameRightKanMap : nerve (AsSmall.{u + 1} SimplexCategory) ⟶
    rightKanShape (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (cofibrantHammockVertex A X) :=
  frameRightKanMap (cofibrantDKSourceFrame A X) (cofibrantDKSourceFrameAugmentation A X)
    (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (cofibrantSourceFrameAugmentation_invertible A X)

lemma cofibrantSourceFrameRightKanMap_projection : cofibrantSourceFrameRightKanMap A X ≫
    rightKanProjection (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (cofibrantHammockVertex A X) = nerveMap (cofibrantDKSourceFrame A X) :=
  frameRightKanMap_projection _ _ _ _

lemma cofibrantSourceFrameRightKanMap_initial (n : (nerve
    (AsSmall.{u + 1} SimplexCategory)) _⦋0⦌) :
    IsInitialVertex ((cofibrantSourceFrameRightKanMap A X ≫
      CategoryTheory.Limits.pullback.fst _ _).app (op ⦋0⦌) n) :=
  frameRightKanMap_coslice_initial _ _ _ _ n

lemma cofibrantSourceFrameRightKanMap_diagram {E : SSet.{u + 1}}
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E) :
    cofibrantSourceFrameRightKanMap A X ≫
        rightKanDiagram (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) F
          (cofibrantHammockVertex A X) = nerveMap (cofibrantDKSourceFrame A X) ≫ F :=
  frameRightKanMap_diagram _ _ _ _ F

def cofibrantSourceFrameRightKanTotalMap :
    nerve (Total (cofibrantDKSourceFrame A X)) ⟶
      rightKanShape (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A X) :=
  rightKanMap (cofibrantDKSourceFrame A X) (cofibrantDKSourceFrameAugmentation A X)
    (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (cofibrantSourceFrameAugmentation_invertible A X)

lemma cofibrantSourceFrameRightKanTotalMap_projection :
    cofibrantSourceFrameRightKanTotalMap A X ≫
      rightKanProjection (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A X) = nerveMap (target (cofibrantDKSourceFrame A X)) :=
  rightKanMap_projection _ _ _ _

lemma cofibrantSourceFrame_hasLimit {E : SSet.{u + 1}} [SSet.Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A))) :
    HasLimit (nerveMap (cofibrantDKSourceFrame A X) ≫ F) :=
  (target_hasLimit_iff _ F).mp (cofibrantSourceFrameTotal_hasLimit A X F hF)

end SerrePositivity.EInfinity.BarrattEccles

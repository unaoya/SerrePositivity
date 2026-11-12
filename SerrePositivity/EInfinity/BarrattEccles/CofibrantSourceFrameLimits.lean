module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrame
public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.EInfinity.SimplicialLocalization.HammockInvertsEdges

/-!
# 元の cofibrant source frame の全矢図式の実 ∞ 極限

概要：任意の元の擬同型反転関手に対し、全 frame 矢の図式の極限を供給する。
方針：同じ augmentation・全成分の弱同値・次数圏の可縮性を一般定理へ渡す。
規約：任意可換環・任意 quasicategory 標的。右 Kan 形状への cofinal 比較は別工程。
使われ方：CAlg_R の局所化普遍性の実局所極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories
open SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CofibrantAlgebra A)

def cofibrantDKSourceFrameAugmentation : cofibrantDKSourceFrame A X ⟶
    (Functor.const (AsSmall.{u + 1} SimplexCategory)).obj
      (show (cofibrantAlgebraRelativeCategory A).category from X) where
  app n := ⟨(cofibrantSourceFrameAugmentation A X).app (ULift.down n)⟩
  naturality _ _ f := by
    apply ULift.ext
    exact (cofibrantSourceFrameAugmentation A X).naturality (ULift.down f)

lemma cofibrantDKSourceFrameAugmentation_weak (n : AsSmall.{u + 1} SimplexCategory) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantDKSourceFrameAugmentation A X).app n) :=
  cofibrantSourceFrameAugmentation_weak A X (ULift.down n)

lemma sourceFrameIndex_weaklyContractible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (AsSmall.{u + 1} SimplexCategory)) := by
  let t : AsSmall.{u + 1} SimplexCategory := ⟨⦋0⦌⟩
  have ht : CategoryTheory.Limits.IsTerminal t :=
    CategoryTheory.Limits.IsTerminal.ofUniqueHom
      (fun (n : AsSmall.{u + 1} SimplexCategory) =>
        ⟨SimplexCategory.isTerminalZero.from (ULift.down n)⟩)
      (fun _ _ => ULift.ext (Subsingleton.elim _ _))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveVertex_isTerminal ht).isWeaklyContractible

lemma cofibrantSourceFrameTotal_hasLimit {E : SSet.{u + 1}} [SSet.Quasicategory E]
    (F : nerve (cofibrantAlgebraRelativeCategory A).category ⟶ E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges (cofibrantAlgebraRelativeCategory A))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target (cofibrantDKSourceFrame A X)) ≫ F) := by
  apply FrameHom.FrameArrows.target_hasLimit_of_inverting_augmentation
    (cofibrantDKSourceFrame A X) (cofibrantDKSourceFrameAugmentation A X) F
  · intro n
    have hw := hF (show ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n) ∈
        weakNerveEdges (cofibrantAlgebraRelativeCategory A) from
      ⟨_, _, _, cofibrantDKSourceFrameAugmentation_weak A X n, rfl⟩)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
        ((SSet.truncation 2).map F)) at hw
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ ((cofibrantDKSourceFrameAugmentation A X).app n))).map
        ((SSet.truncation 2).map F))
      (f := ((nerve.edgeMk ((cofibrantDKSourceFrameAugmentation A X).app n)).map F).toTruncated)
      rfl).mp hw
  · exact sourceFrameIndex_weaklyContractible.{u}

end SerrePositivity.EInfinity.BarrattEccles

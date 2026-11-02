module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorKernelEdges
public import SerrePositivity.InfinityCategories.Stable.UniverseKernelImage
public import SerrePositivity.InfinityCategories.Stable.UniverseExactFunctorLift
public import SerrePositivity.InfinityCategories.Stable.Idempotent.StabilityUniverse
/-!
概要：核包含の cofiber 辺と商の反転辺の一致を任意の追加 ULift 宇宙で得る。
方針：零対象核の本質像判定・完全性・安定性を同じ宇宙へ持ち上げて判定する。
規約：既存の安定性持ち上げ入口を読み取り専用で使い、局所化は別に扱う。
使われ方：D-16 の共通宇宙での thick 核の辺集合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {A X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (i : A ⟶ X) (F : X ⟶ Y) [IsExactFunctor F]
  (h : ∀ x : X _⦋0⦌, IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) ↔
    ∃ a : A _⦋0⦌, Nonempty (VertexIso (i.app (Opposite.op ⦋0⦌) a) x))
include h

lemma cofiberLocalizingEdges_ulift_essentialImage_eq_invertedEdges :
    cofiberLocalizingEdges
      {x | ∃ a : ((SSet.uliftFunctor.{v}).obj A) _⦋0⦌,
        Nonempty (VertexIso (((SSet.uliftFunctor.{v}).map i).app (Opposite.op ⦋0⦌) a) x)} =
      invertedEdges ((SSet.uliftFunctor.{v}).map F) := by
  let := F2.Idempotent.isStable_ulift.{u, v} (X := X)
  let := F2.Idempotent.isStable_ulift.{u, v} (X := Y)
  let := isExactFunctor_ulift F (inferInstance : IsExactFunctor F)
  exact cofiberLocalizingEdges_eq_invertedEdges_of_kernel ((SSet.uliftFunctor.{v}).map F) _
    (zeroKernel_ulift_iff_essentialImage i F h)

end SerrePositivity.InfinityCategories

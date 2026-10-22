module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowLimits
public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeFamilyUnderlying
public import SerrePositivity.InfinityCategories.Derived.WeaklyContractibleConstantLimit
public import SerrePositivity.InfinityCategories.Derived.LimitDiagramIso
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing

/-!
# 元の augmentation を反転する関手の全矢図式の実極限

概要：元の augmentation の円柱を反転関手で送り、同じ値の定値図式へ比較する。
方針：全成分の可逆性で関手同型を作り、可縮な次数圏の実極限を移送する。
規約：任意 quasicategory 標的。対象ごとの同型の族で全関手同型を代用しない。
使われ方：source frame の右 Kan 局所図式へ移すための実極限の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (F : nerve C ⟶ E)
  (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)

def augmentationHomotopy : SSet.Homotopy (nerveMap A ≫ F)
    (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex X))) :=
  stableHomotopyRetarget
    (HomotopyClasses.postHomotopy F (F1B.kanNerveNatTransHomotopy p)) rfl
    (by rw [F1B.kanNerveMap_const, SSet.const_comp])

def augmentationFunctorIso :
    FunctorIso (nerveMap A ≫ F) (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  let H := augmentationHomotopy A p F
  apply functorIsoOfPointwiseInvertibleHomotopy H
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  have he : (simplicialHomotopyVertexEdge H (nerveVertex i)).edge =
      ((nerve.edgeMk (p.app i)).map F).edge := by
    change F.app _ ((simplicialHomotopyVertexEdge
      (F1B.kanNerveNatTransHomotopy p) (nerveVertex i)).edge) = _
    exact congrArg (F.app _) (F1B.kanNerveNatTransHomotopy_component p i)
  exact (isInvertibleEdge_congr he).mpr (hp i)

lemma augmentationFunctorIso_hom : (augmentationFunctorIso A p F hp).hom =
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (augmentationHomotopy A p F)) := rfl

include hp in
lemma target_hasLimit_of_inverting_augmentation (hI : IsWeaklyContractible (nerve I)) :
    HasLimit (nerveMap (target A) ≫ F) := by
  apply (target_hasLimit_iff A F).mpr
  apply (hasLimit_iff_of_functorIso (augmentationFunctorIso A p F hp)).mpr
  exact ⟨constantDiagramCone _ E _, constantDiagramCone_isLimit _ E hI _⟩

end SerrePositivity.EInfinity.FrameHom.FrameArrows

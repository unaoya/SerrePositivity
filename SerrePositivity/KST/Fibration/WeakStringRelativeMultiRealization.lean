module
public import SerrePositivity.KST.Fibration.WeakStringRelativeCoreRealization
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity

/-! # 元の相対 S 対角を全長の有限加法性の単回実現へ接続する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の単回 core S 実現と既存の反復実現の一回の場合の、全 W 列に自然な同型。 -/
def weakStringCoreSingleRealizationIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringStableSimplicial q ⋙ coreSRealizationFunctor ≅ weakStringMultiRealization q 1 :=
  NatIso.ofComponents (fun n => coreSingleRealizationIso (weakStringModel q n.unop)) (by
    intro m n θ
    exact coreSingleRealizationIso_naturality (weakStringExactMap q θ.unop))

/-- 元の相対 S の対角から、元の全 W 列の単回反復実現の対角への実比較射。 -/
def relativeSWeakStringMultiComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) ⟶
      simplicialDiagonalFunctor.obj (weakStringMultiRealization q 1) :=
  relativeSWeakStringCoreComparison q ≫
    simplicialDiagonalFunctor.map (weakStringCoreSingleRealizationIso q).hom

/-- 全長の有限加法性の入力と同じ実現模型への元の実比較は局所化同型。 -/
theorem relativeSWeakStringMultiComparison_localized_isIso
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeSWeakStringMultiComparison q)) := by
  have := relativeSWeakStringCoreComparison_localized_isIso q
  unfold relativeSWeakStringMultiComparison
  rw [Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration

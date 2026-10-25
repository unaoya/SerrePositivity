module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitMappingKan
public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible

/-!
概要：随伴単位の両射影の inner fibration 性と固定ファイバーの Kan 性。
方針：core の厳密同型と全部分複体の包含を使い、辺の可逆性をファイバーへ反映する。
規約：可縮性や QCat 同値性はここでは主張しない。
使われ方：射影の高次ファイバーを写像空間として比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

instance adjointUnitUnderlying_innerFibration (C D : PresentableInfinityObject.{u}) :
    InnerFibration (adjointUnitUnderlying C D) := by
  change InnerFibration ((adjointUnitCoreIso C D).hom ≫
    (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x))).ι)
  exact ⟨innerFibrations.comp_mem _ _ (innerFibrations.of_isIso _)
    (InnerFibration.mem (q := (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x))).ι))⟩

instance adjointUnitLeft_innerFibration (C D : PresentableInfinityObject.{u}) :
    InnerFibration (adjointUnitLeft C D) := by
  unfold adjointUnitLeft
  exact ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q := adjointUnitUnderlying C D))
    (innerFibrations.comp_mem _ _ (InnerFibration.mem (q := pullback.snd _ (unitComposition C D)))
      (InnerFibration.mem (q := CartesianMonoidalCategory.fst _ _)))⟩

instance adjointUnitRight_innerFibration (C D : PresentableInfinityObject.{u}) :
    InnerFibration (adjointUnitRight C D) := by
  unfold adjointUnitRight
  exact ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q := adjointUnitUnderlying C D))
    (innerFibrations.comp_mem _ _ (InnerFibration.mem (q := pullback.snd _ (unitComposition C D)))
      (InnerFibration.mem (q := CartesianMonoidalCategory.snd _ _)))⟩

/-- 概要：Kan 全空間からの inner fibration の各頂点ファイバーは Kan。
方針：inner fiber の quasicategory 性と包含による辺の可逆性の反映を使う。
規約：底は quasicategory でよく、全ホーンの相対充填性は要求しない。
使われ方：随伴単位の両射影の固定ファイバー。 -/
lemma innerFiberOfKan_kanComplex {E B : SSet.{u}} [KanComplex E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (b : B _⦋0⦌) : KanComplex (vertexFiber p b) := by
  have : IsGroupoid (hoFunctor.obj (vertexFiber p b)) := by
    constructor
    intro x y f
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective (X := vertexFiber p b) x y f
    exact (isInvertibleEdge_vertexFiber_iff p b e).mpr
      (IsGroupoid.all_isIso (C := hoFunctor.obj E) _)
  exact kanComplex_of_isGroupoid _

instance adjointUnitLeftFiber_kanComplex (C D : PresentableInfinityObject.{u})
    (v : PrLMappingSpace C D _⦋0⦌) : KanComplex (vertexFiber (adjointUnitLeft C D) v) :=
  innerFiberOfKan_kanComplex _ _

instance adjointUnitRightFiber_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) : KanComplex (vertexFiber (adjointUnitRight C D) w) :=
  innerFiberOfKan_kanComplex _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality

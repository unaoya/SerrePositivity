module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSimplicialCodes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable

/-!
概要：有限な全空間を持つ底上の全対象を、同じ小さい宇宙で同型まで符号化する。
方針：共通の有限単体集合の符号に底への射を添え、元の底上の対象との同型を戻す。
規約：底は任意。対象の全空間だけでなく、底への元の射も保持する。
使われ方：前層の小さい compact 生成族に用いる有限底上模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 固定した小さい底上の、全有限模型の共通の小さい符号型。 -/
def FiniteOverCode (B : SSet.{u}) : Type u :=
  Σ q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSimplicialCode.{u}, q.realization ⟶ B

/-- 符号の底上の元の宇宙での実現。 -/
def FiniteOverCode.realization {B : SSet.{u}} (q : FiniteOverCode B) : Over B :=
  Over.mk q.2

instance finiteOverCode_realization_finite {B : SSet.{u}} (q : FiniteOverCode B) :
    q.realization.left.Finite := by
  change q.1.realization.Finite
  infer_instance

/-- 底上の任意の有限全空間は、共通の小さい符号の一つと底上で同型。 -/
lemma exists_finiteOverCode {B : SSet.{u}} (A : Over B) [A.left.Finite] :
    ∃ q : FiniteOverCode B, Nonempty (q.realization ≅ A) := by
  obtain ⟨q, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_finiteSimplicialCode A.left
  refine ⟨⟨q, e.hom ≫ A.hom⟩, ⟨Over.isoMk e ?_⟩⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

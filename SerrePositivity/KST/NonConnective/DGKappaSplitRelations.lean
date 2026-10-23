module

public import SerrePositivity.KST.NonConnective.DGKappaSplitProjections
public import SerrePositivity.KST.NonConnective.DGSumPairSplit

/-!
概要：同じ dg 関手 Hom end 内での、id ⊕ T の実分裂関係。
方針：全対象評価の識別性で元の実直和の四合成と恒等分解へ戻す。
規約：全関手の閉射の等式として保持する。使われ方：全 native Perf 作用の分裂族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ全 Hom end での左注入・左射影の分裂。 -/
lemma dgKappaSplit_head_head :
    dgKappaSplitHead R D I ≫ dgKappaSplitHeadProjection R D I = 𝟙 _ := by
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  simp only [dgKappaSplitHead, dgKappaSplitHeadProjection, dgFunctorClosedHomFromFamily_eval]
  exact dgSumPair_left_left R D (dgSwindleSummand R D) X.val

/-- 同じ全 Hom end での右注入・左射影の交差合成は零。 -/
lemma dgKappaSplit_tail_head :
    dgKappaSplitTail R D I ≫ dgKappaSplitHeadProjection R D I = 0 := by
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
  simp only [dgKappaSplitTail, dgKappaSplitHeadProjection, dgFunctorClosedHomFromFamily_eval]
  exact dgSumPair_right_left R D (dgSwindleSummand R D) X.val

/-- 同じ全 Hom end での左注入・右射影の交差合成は零。 -/
lemma dgKappaSplit_head_tail :
    dgKappaSplitHead R D I ≫ dgKappaSplitTailProjection R D I = 0 := by
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
  simp only [dgKappaSplitHead, dgKappaSplitTailProjection, dgFunctorClosedHomFromFamily_eval]
  exact dgSumPair_left_right R D (dgSwindleSummand R D) X.val

/-- 同じ全 Hom end での右注入・右射影の分裂。 -/
lemma dgKappaSplit_tail_tail :
    dgKappaSplitTail R D I ≫ dgKappaSplitTailProjection R D I = 𝟙 _ := by
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  simp only [dgKappaSplitTail, dgKappaSplitTailProjection, dgFunctorClosedHomFromFamily_eval]
  exact dgSumPair_right_right R D (dgSwindleSummand R D) X.val

/-- 元の二項直和の恒等分解を、同じ全 dg 関手 Hom end 内に保持する。 -/
lemma dgKappaSplit_decomposition :
    dgKappaSplitHeadProjection R D I ≫ dgKappaSplitHead R D I +
      dgKappaSplitTailProjection R D I ≫ dgKappaSplitTail R D I = 𝟙 _ := by
  apply dgFunctorClosedHom_ext R (DGKappaCone R D I) (DGKappaCone R D I)
  intro X
  rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  simp only [dgKappaSplitHead, dgKappaSplitTail, dgKappaSplitHeadProjection,
    dgKappaSplitTailProjection, dgFunctorClosedHomFromFamily_eval]
  exact dgSumPair_decomposition R D (dgSwindleSummand R D) X.val

end SerrePositivity.KST.NonConnective

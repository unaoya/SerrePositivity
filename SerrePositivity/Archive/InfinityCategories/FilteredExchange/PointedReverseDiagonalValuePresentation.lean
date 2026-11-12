module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseKanDiagonalValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：元の反転全対角の値比較を、元の F1 の同じ実合成 prism の指定比較へ戻す。
方針：元の fiber・左区間の表示変更だけを除去する。
規約：元の指定比較を保持。使われ方：固定射成分と元の実長辺の比較の値照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {P : SSet.{u + 1}} (K L : KanObject.{u})
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom pointKanObject K).op)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
local notation "D" => pointedReverseKanCompositionTransport_diagonalIso K L
  (x ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)))
  (y ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom K L)))
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))

/-- 元の全反転対角の値比較は、元の F1 の同じ合成 prism の指定比較の値そのもの。 -/
lemma pointedReverseKanDiagonalValueIso_heq_diagonal :
    HEq (pointedReverseKanDiagonalValueIso K L x y) (FunctorIso.postcomp D V) := by
  unfold pointedReverseKanDiagonalValueIso
  change HEq (Eq.mp _ (FunctorIso.postcomp D V)) (FunctorIso.postcomp D V)
  have hcast {α β : Sort (u + 2)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 同じ指定値の全係数制限も、元の同じ合成 prism の比較の値の制限。 -/
lemma pointedReverseKanDiagonalValueIso_precomp_heq_diagonal
    {Q : SSet.{u + 1}} (r : Q ⟶ P) :
    HEq ((pointedReverseKanDiagonalValueIso K L x y).precomp r)
      ((FunctorIso.postcomp D V).precomp r) := by
  have hx : (x ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom) ≫
      pointedReverseKanFiberComparison K = x ≫ pointedCoherentFiberComparison K ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent K).symm) := by
    rw [Category.assoc, pointedReverseKanFiberComparison_normalized]
  have hy : (y ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
      intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
        (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) =
      y ≫ coherentKanLeftHomInterval K L := by
    rw [← coherentKanLeftHomInterval_reverse]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact functorIso_precomp_heq_of_heq (FunctorIso.postcomp D V)
    (pointedReverseKanDiagonalValueIso K L x y) rfl (by rw [hx, hy])
    (pointedReverseKanDiagonalValueIso_heq_diagonal K L x y) r

end SerrePositivity.InfinityCategories.F2

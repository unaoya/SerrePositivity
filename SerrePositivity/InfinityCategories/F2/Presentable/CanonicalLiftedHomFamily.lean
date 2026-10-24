module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits

/-!
概要：元の標準左 Kan 余錐から持ち上げた全 Hom 族の右 Kan 条件。
方針：同じ標的全体を一段持ち上げ、余極限を反転して全 co-Yoneda へ送る。
規約：始域を P_Σ に限定せず、元の全係数族を保持する。
使われ方：Ind 延長と幾何学的実現を組み合わせる全自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の関手の全 Hom を標的全体の宇宙変更後に束ねる。
方針：持ち上げた関手の反対を全 co-Yoneda へ合成する。
規約：全ての標的係数に自然な関手族とする。
使われ方：Ind と P_Σ に共通の Hom 表示。 -/
def canonicalLiftedHomFamily {A D : SSet.{u}} [Quasicategory D] (G : A ⟶ D) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 2, u + 1}).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj D))).obj SpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map G)) ≫
    coyonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj D)

/-- 概要：全標準左 Kan 余錐の普遍性は同じ全 Hom 族の右 Kan 条件を与える。
方針：宇宙比較した全余錐を反転して co-Yoneda で極限へ送る。
規約：元の射・関手と同じ恒等右 Kan 単位を保持する。
使われ方：filtered 延長の全 Hom 族と前層係数族の比較。 -/
lemma canonicalLiftedHomFamily_isRightKanExtension
    {K A D : SSet.{u}} [Quasicategory D] (δ : K ⟶ A) (G : A ⟶ D)
    (hG : ∀ a, IsColimitCone (leftKanCanonicalCocone δ G a)) :
    IsRightKanExtension
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 1, u}).map δ)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 1, u}).map δ)) ≫ canonicalLiftedHomFamily G)
      (canonicalLiftedHomFamily G)
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 1, u}).map δ)) ≫ canonicalLiftedHomFamily G)) := by
  apply rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have hcan : IsColimitCone (leftKanCanonicalCocone
      ((SSet.uliftFunctor.{u + 1, u}).map δ) ((SSet.uliftFunctor.{u + 1, u}).map G)
      (SSet.opObjEquiv c)) := by
    rcases SSet.opObjEquiv c with ⟨a⟩
    exact (leftKanCanonicalCocone_isColimit_iff_ulift δ G a).mp (hG a)
  have hc := rightKanCanonicalCone_op_isLimit _ _ (SSet.opObjEquiv c) hcan
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at hc
  exact coyonedaInfinityMap_map_isLimit _ hc

end SerrePositivity.InfinityCategories.F2.Presentable

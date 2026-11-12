module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalTransportValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の余錐の区間 Hom 比較の各点成分を、同じ定値図式輸送比較の制限へ戻す。
方針：両端の全射を揃え、元の curry と同じ係数の評価を順に移す。
規約：元の単位と指定比較を保持。使われ方：既存の下側輸送因子への因子消去の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}}
  (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace c.vertex z)
local notation "E" => leftUnstraightening F
local notation "P" => constantUnstraighteningFiberProjection B c.vertex
local notation "S" => coconeIntervalTransportSource c T

/-- 元の Hom 比較の一点成分は、同じ定値輸送比較の同じ係数・二座標への制限。 -/
lemma coconeIntervalFiberHomIso_app_heq_constant (l : T _⦋0⦌) :
    HEq ((coconeIntervalFiberHomIso c a).app l)
      ((constantDiagramMappingTransportIso B a).precomp
        (lift (𝟙 E) (SSet.const l) ≫ S)) := by
  have ht : curry (lift (fst E T ≫ coconeFiberMap c) (snd E T) ≫
      (pointedIntervalTransport a).endpoint) =
      (pointedIntervalTransport a).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_pre_app]
    change _ = (coconeFiberMap c ▷ T) ≫ uncurry (curry (pointedIntervalTransport a).endpoint)
    rw [uncurry_curry]
    rfl
  have he := functorIso_app_heq_of_heq (coconeIntervalFiberHomIso c a)
    (coconeIntervalFiberTransportIso c a).curry (curry_uncurry _).symm ht.symm
    (coconeIntervalFiberHomIso_heq_curry c a) l
  refine he.trans ((functorIso_curry_app_heq_precomp
    (coconeIntervalFiberTransportIso c a) l).trans ?_)
  have htarget : S ≫ ((P ▷ T) ≫ (pointedIntervalTransport a).endpoint) =
      lift (fst E T ≫ coconeFiberMap c) (snd E T) ≫ (pointedIntervalTransport a).endpoint :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ (pointedIntervalTransport a).endpoint)
        (coconeIntervalTransportSource_projection c T))
  refine (functorIso_precomp_heq_of_heq
    ((constantDiagramMappingTransportIso B a).precomp S) (coconeIntervalFiberTransportIso c a)
    (coconeIntervalRelativeComposite_coordinates c a).symm htarget
    (coconeIntervalFiberTransportIso_heq_constant c a)
    (lift (𝟙 E) (SSet.const l))).trans ?_
  exact heq_of_eq (functorIso_precomp_precomp (constantDiagramMappingTransportIso B a)
    S (lift (𝟙 E) (SSet.const l)))

end SerrePositivity.InfinityCategories.F2

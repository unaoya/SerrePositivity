module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackHomRestriction
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorCoreColimitDescent

/-!
概要：底を覆う任意の小さい余極限について、元の cocartesian Hom の core の族を回収する。
方針：実際の底変換の全空間の余極限と、元の指定辺の保存・被覆を降下定理へ渡す。
規約：辺の被覆を追加仮定にせず、元の底の余極限から実際に証明した条件を使う。
使われ方：元の分類主写像の Hom 空間を底の単体・セルで比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] [Small.{u} J]
  {T E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [InnerFibration q]
  (D : J ⥤ Over B) (hc : IsColimit ((Over.forgetCocone B).whisker D))
  (s : ∀ j, T ⟶ (quasicategoryCore (cocartesianPullbackHomSpace p q (D.obj j)) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ quasicategoryCoreMap (cocartesianPullbackHomPre p q (D.map f)))

/-- 底を覆う各引き戻し上の整合する core の族を、元の全 cocartesian Hom の core に貼る。 -/
def cocartesianPullbackHomCoreColimitLift :
    T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}) :=
  markedCocartesianCoreFamilyColimitLift q (cocartesianPullbackDomainDiagram p D)
    (cocartesianPullbackDomainMark p D) (cocartesianPullbackDomainMark_map p D) s hs
    (cocartesianPullbackDomainCocone p D) (cocartesianPullbackDomainCocone_isColimit p D hc)
    {e | IsCocartesianEdge p e} (cocartesianPullbackDomainMark_cover p D hc)
    (cocartesianPullbackDomainMark_cocone p D)

/-- 貼った同じ core の族は、底の各項への元の制限を厳密に回収する。 -/
lemma cocartesianPullbackHomCoreColimitLift_fac (j : J) :
    cocartesianPullbackHomCoreColimitLift p q D hc s hs ≫
      quasicategoryCoreMap (cocartesianPullbackHomRestriction p q (D.obj j)) = s j :=
  markedCocartesianCoreFamilyColimitLift_fac q (cocartesianPullbackDomainDiagram p D)
    (cocartesianPullbackDomainMark p D) (cocartesianPullbackDomainMark_map p D) s hs
    (cocartesianPullbackDomainCocone p D) (cocartesianPullbackDomainCocone_isColimit p D hc)
    _ (cocartesianPullbackDomainMark_cover p D hc) (cocartesianPullbackDomainMark_cocone p D) j

/-- 底の各項上で同じ族を回収する、元の全体上の cocartesian Hom の core の族は一意。 -/
lemma cocartesianPullbackHomCoreColimitLift_unique
    (m : T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace p q) : SSet.{u}))
    (hm : ∀ j, m ≫ quasicategoryCoreMap (cocartesianPullbackHomRestriction p q (D.obj j)) = s j) :
    m = cocartesianPullbackHomCoreColimitLift p q D hc s hs :=
  markedCocartesianCoreFamilyColimitLift_unique q (cocartesianPullbackDomainDiagram p D)
    (cocartesianPullbackDomainMark p D) (cocartesianPullbackDomainMark_map p D) s hs
    (cocartesianPullbackDomainCocone p D) (cocartesianPullbackDomainCocone_isColimit p D hc)
    _ (cocartesianPullbackDomainMark_cover p D hc) (cocartesianPullbackDomainMark_cocone p D) m hm

end SerrePositivity.InfinityCategories

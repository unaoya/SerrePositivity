module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativePrecomposition
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorCoreColimitDescent

/-!
概要：元の全 cocartesian 相対 Hom の core の族を、cocartesian 辺を覆う余極限へ降下させる。
方針：指定辺を保つ Hom の降下で、各射影の元の cocartesian 辺の集合を指定する。
規約：辺の被覆と各脚の辺の保存を明示し、全体と各項の元の射影を保持する。
使われ方：分類主写像の元の Hom 空間のセルごとの比較。
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
  {T E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q] (D : J ⥤ Over B)
  (hD : ∀ {j k} (f : j ⟶ k),
    PreservesCocartesianEdges (D.obj j).hom (D.obj k).hom (D.map f).left)
  (s : ∀ j, T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace (D.obj j).hom q) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ quasicategoryCoreMap (cocartesianRelativeFunctorPre q (D.map f) (hD f)))
  (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
  (hcover : ∀ e, IsCocartesianEdge c.pt.hom e → ∃ j t,
    IsCocartesianEdge (D.obj j).hom t ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
  (hi : ∀ j, PreservesCocartesianEdges (D.obj j).hom c.pt.hom (c.ι.app j).left)

/-- 整合する元の全 cocartesian Hom の core の族を、同じ余極限上へ貼る。 -/
def cocartesianRelativeCoreFamilyColimitLift :
    T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace c.pt.hom q) : SSet.{u}) :=
  markedCocartesianCoreFamilyColimitLift q D (fun j ↦ {e | IsCocartesianEdge (D.obj j).hom e})
    hD s hs c hc {e | IsCocartesianEdge c.pt.hom e} hcover hi

/-- 貼った元の cocartesian Hom の core の族は、各項の指定された族を厳密に回収する。 -/
lemma cocartesianRelativeCoreFamilyColimitLift_fac (j : J) :
    cocartesianRelativeCoreFamilyColimitLift q D hD s hs c hc hcover hi ≫
      quasicategoryCoreMap (cocartesianRelativeFunctorPre q (c.ι.app j) (hi j)) = s j :=
  markedCocartesianCoreFamilyColimitLift_fac q D _ hD s hs c hc _ hcover hi j

/-- 各項で同じ族を回収する、元の全体上の cocartesian Hom の core の族は一意。 -/
lemma cocartesianRelativeCoreFamilyColimitLift_unique
    (m : T ⟶ (quasicategoryCore (cocartesianRelativeFunctorSpace c.pt.hom q) : SSet.{u}))
    (hm : ∀ j, m ≫ quasicategoryCoreMap (cocartesianRelativeFunctorPre q (c.ι.app j) (hi j)) = s
      j) :
    m = cocartesianRelativeCoreFamilyColimitLift q D hD s hs c hc hcover hi :=
  markedCocartesianCoreFamilyColimitLift_unique q D _ hD s hs c hc _ hcover hi m hm

end SerrePositivity.InfinityCategories

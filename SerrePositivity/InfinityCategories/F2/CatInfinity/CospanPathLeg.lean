module
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleFunctorEdgePath
/-!
概要：一つの全関手同型で可換な脚を、両入力の可逆 path 置換の間の厳密な脚へ移す。
方針：元の可換同型と入力置換の指定同型を合成し、同じ全 path を引き戻しへ入れる。
規約：元の射影・終点を厳密に保持する。使われ方：関手同型付き cospan の strict 化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits SSet
open scoped Simplicial
variable {A C A' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory C] [Quasicategory A'] [Quasicategory C']
  (p : A ⟶ C) (p' : A' ⟶ C') (a : A ⟶ A') (c : C ⟶ C')
  (hp : FunctorIso (p ≫ c) (a ≫ p'))

def cospanPathLegIso :
    FunctorIso ((equivalencePathReplacementProjection a ≫ p) ≫ c)
      (equivalencePathReplacementMap a ≫ p') := by
  have h : FunctorIso ((equivalencePathReplacementProjection a ≫ p) ≫ c)
      ((equivalencePathReplacementProjection a ≫ a) ≫ p') := by
    simpa only [FunctorIso, Category.assoc] using hp.precomp (equivalencePathReplacementProjection a)
  exact h.trans ((equivalencePathReplacementFunctorIso a).postcomp p')

def cospanPathLeg : equivalencePathReplacement a ⟶ equivalencePathReplacement c :=
  pullback.lift
    (invertibleFunctorEdgePath (cospanPathLegIso p p' a c hp).edge
      (cospanPathLegIso p p' a c hp).edge_isInvertible)
    (equivalencePathReplacementProjection a ≫ p)
    (invertibleFunctorEdgePath_zero _ _)

lemma cospanPathLeg_projection :
    cospanPathLeg p p' a c hp ≫ equivalencePathReplacementProjection c =
      equivalencePathReplacementProjection a ≫ p := pullback.lift_snd _ _ _

lemma cospanPathLeg_map :
    cospanPathLeg p p' a c hp ≫ equivalencePathReplacementMap c =
      equivalencePathReplacementMap a ≫ p' := by
  rw [equivalencePathReplacementMap, ← Category.assoc, cospanPathLeg,
    pullback.lift_fst, invertibleFunctorEdgePath_one]

end SerrePositivity.InfinityCategories.F2

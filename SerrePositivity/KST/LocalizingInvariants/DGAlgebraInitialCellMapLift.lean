module

public import SerrePositivity.KST.LocalizingInvariants.CochainCycleCoverMapLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSuccessorCellPrimitives

/-!
概要：自由初期 cell 代数からの任意の射を全射擬同型に沿って持ち上げる。
方針：元の生成辺への制限を持ち上げ、既存の自由 dg 圏の普遍性で延長する。
規約：増大射に限定せず、元の射との厳密な合成を保つ。
使われ方：cell 源の任意の写像の持ち上げの初期段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  (g : cellStage R A 0 ⟶ B)

def initialCellMapTargetFunctor :
    DGFunctor R (DGCategoryCycleCover.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) where
  obj _ := .star
  map x y := by cases x; cases y; exact g.hom
  map_id x := by cases x; exact IsMonHom.one_hom g.hom
  map_comp x y z := by cases x; cases y; cases z; exact IsMonHom.mul_hom g.hom

def initialCellMapLiftEdge (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) :
    DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) x y ⟶ C.X := by
  cases x; cases y
  exact cycleCoverMapLift p.hom hs hq
    (FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) .star .star ≫ g.hom)

lemma initialCellMapLiftEdge_projection (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) :
    initialCellMapLiftEdge R p hs hq g x y ≫ p.hom =
      FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)
        (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) x y ≫
          (initialCellMapTargetFunctor R g).map x y := by
  cases x; cases y
  exact cycleCoverMapLift_projection p.hom hs hq _

def initialCellMapLiftFunctor :
    DGFunctor R (DGCategoryCycleCover.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C) :=
  FreeDGCategory.lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
    (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) (fun _ => .star)
    (initialCellMapLiftEdge R p hs hq g)

lemma initialCellMapLiftFunctor_projection :
    (initialCellMapLiftFunctor R p hs hq g).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R p) =
      initialCellMapTargetFunctor R g := by
  apply (FreeDGCategory.universalEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)
    (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A))).injective
  apply dgAlgebraGeneratorMap_ext
  intro x y
  change FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) x y ≫
        ((initialCellMapLiftFunctor R p hs hq g).map x y ≫ p.hom) = _
  rw [← Category.assoc]
  change (FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) x y ≫
        (FreeDGCategory.lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
          (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) (fun _ => .star)
          (initialCellMapLiftEdge R p hs hq g)).map x y) ≫ p.hom = _
  rw [FreeDGCategory.lift_edge]
  exact initialCellMapLiftEdge_projection R p hs hq g x y

def initialCellMapLift : cellStage R A 0 ⟶ C :=
  let F := initialCellMapLiftFunctor R p hs hq g
  Mon.Hom.mk' (F.map .star .star) (F.map_id .star) (F.map_comp .star .star .star)

lemma initialCellMapLift_projection : initialCellMapLift R p hs hq g ≫ p = g := by
  apply Mon.Hom.ext'
  exact congrArg (fun F : DGFunctor R
      (DGCategoryCycleCover.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) =>
      (show (cellStage R A 0).X ⟶ B.X from F.map .star .star))
    (initialCellMapLiftFunctor_projection R p hs hq g)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

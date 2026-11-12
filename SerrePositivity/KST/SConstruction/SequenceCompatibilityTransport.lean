module
public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 指定した列の射に沿う実適合辺の移送
概要：段の比較の実適合辺を、構造射と厳密可換な指定射の前合成で移す。
方針：写像空間の源の制限と、指定した列の射の厳密な可換式を使う。
規約：元の適合辺そのものを写し、新しいホモトピー代表を選ばない。
使われ方：元の K の単射置換の射影に沿う実適合辺の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 元の実適合辺を、指定した列の射で源だけ前合成する。 -/
def sequenceCompatibilityEdge_precompose {A B C : KanSequence.{u}} (p : KanSequence.Hom A B)
    (f : ∀ n, (B.level n).space ⟶ (C.level n).space) (n : ℕ)
    (e : (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (B.level n).space) (C.level (n + 1)).space).right.Edge
      (familyVertex (B.sigma n ≫ f (n + 1)))
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n))) :
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (A.level n).space) (C.level (n + 1)).space).right.Edge
      (familyVertex (A.sigma n ≫ (p.app (n + 1) ≫ f (n + 1))))
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ (p.app n ≫ f n) ≫ C.sigma n)) := by
  let q := PointedSimplicialSet.circle.{u} ◁ p.app n
  let Z := (C.level (n + 1)).space
  refine (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre q Z)).ofEq ?_ ?_
  · change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q Z).right.app _ (familyVertex (B.sigma n ≫ f (n + 1))) = _
    rw [familyVertex_pre]
    apply congrArg familyVertex
    change (PointedSimplicialSet.circle.{u} ◁ p.app n) ≫ (B.sigma n ≫ f (n + 1)) = _
    rw [← Category.assoc, p.comm n, Category.assoc]
  · change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q Z).right.app _
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n)) = _
    rw [familyVertex_pre]
    apply congrArg familyVertex
    change (PointedSimplicialSet.circle.{u} ◁ p.app n) ≫
      (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n) = _
    rw [← Category.assoc, ← whiskerLeft_comp]

end SerrePositivity.KST.SConstruction

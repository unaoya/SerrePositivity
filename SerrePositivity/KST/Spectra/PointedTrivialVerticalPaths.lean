module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PointedVerticalPaths

/-!
概要：全単射 RLP 射の同じ像を持つ点つき族を、射影が一定の実区間で結ぶ。
方針：源の基点包含を固定した相対垂直ホモトピーを充填し、同じ区間を記録する。
規約：Kan 性不要。使われ方：元の全 Hom の BF 持ち上げの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 全単射 RLP の射で同じ像を持つ族を、同じ像の上で垂直な実区間で結ぶ。 -/
def verticalPathOfRlp {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (f g : A ⟶ E) (h : f ≫ p = g ≫ p) : VerticalPath p f g := by
  letI basepointMono : Mono A.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono A
  have hbase : A.hom ≫ f.right = A.hom ≫ g.right := by rw [Under.w f, Under.w g]
  let hex := MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy p.right hp
    A.hom f.right g.right (congrArg Under.Hom.right h) hbase
  refine VerticalPath.ofHomotopy hex.choose ?_ hex.choose_spec.1
  rw [hex.choose_spec.2, Under.w f]
  rfl

end SerrePositivity.KST.Spectra.PointedMapping

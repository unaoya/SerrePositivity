module
public import SerrePositivity.InfinityCategories.Stable.AdjunctionOppositeCounit
/-!
概要：標準区間条件から作る随伴の余単位を、元の指定ホモトピーの類へ回収する。
方針：全パラメータ Hom 対応の恒等射と、反対側の指定単位の回収を使う。
規約：元の h Fun の射を等式で保持する。使われ方：実 RHom 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed Bicategory SSet
open scoped Simplicial

/-- 標準区間条件で得た随伴の余単位は、指定した同じ実ホモトピーの類。 -/
lemma qcatAdjunctionOfCounitIntervalCondition_counitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H y).toTruncated))) :
    (qcatAdjunctionOfCounitIntervalCondition H h).counitHom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  apply (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (G ≫ F) (𝟙 Y)).injective
  unfold qcatAdjunctionOfCounitIntervalCondition
  rw [qcatAdjunctionOfOpposite_counitHom,
    qcatAdjunctionOfUnitMappingSpaceCondition_unitHom]
  rfl
end SerrePositivity.InfinityCategories

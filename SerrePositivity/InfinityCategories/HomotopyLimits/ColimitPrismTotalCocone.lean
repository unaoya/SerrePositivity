module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitPrismTotalShape
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction
public import SerrePositivity.InfinityCategories.F1.Simplicial.PrismEndpointRightAnodyne

/-!
概要：終点余錐の余極限性から、元の prism の全図式の余錐の余極限性を導く。
方針：join と直積の座標を保ち、元の両端と頂点の射を厳密に照合する。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の余錐間の prism の底図式。 -/
def colimitPrismDiagram {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) : (Δ[1] : SSet.{u}) ⊗ K ⟶ X :=
  ((Δ[1] : SSet.{u}) ◁ joinInl K Δ[0]) ≫ G

/-- 元の余錐間の prism の指定端点の余錐。 -/
def colimitPrismEndpoint {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) (j : Fin 2) :
    JoinCocone (prismEndpoint j K ≫ colimitPrismDiagram G) :=
  ⟨prismEndpoint j (join K Δ[0]) ≫ G, by
    dsimp only [colimitPrismDiagram]
    simp only [← Category.assoc, prismEndpoint_naturality]⟩

/-- 元の prism の底の全図式に対する、終点頂点を持つ余錐。 -/
def colimitPrismTotalCocone {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) : JoinCocone (colimitPrismDiagram G) :=
  ⟨colimitPrismTotalMap K ≫ G, by rw [← Category.assoc, colimitPrismTotalMap_inl]; rfl⟩

/-- 全図式の余錐の終点面への制限は、元の終点余錐そのもの。 -/
lemma colimitPrismTotalCocone_target {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X) :
    (colimitPrismTotalCocone G).restrict (prismEndpoint 1 K) = colimitPrismEndpoint G 1 := by
  apply Subtype.ext
  change joinMap (prismEndpoint 1 K) (𝟙 (Δ[0] : SSet.{u})) ≫
    (colimitPrismTotalMap K ≫ G) = prismEndpoint 1 (join K Δ[0]) ≫ G
  rw [← Category.assoc, colimitPrismTotalMap_target]

/-- 元の終点余錐が余極限なら、同じ頂点の全図式の余錐も余極限。 -/
lemma colimitPrismTotalCocone_isColimit {K X : SSet.{u}} [Quasicategory X]
    (G : (Δ[1] : SSet.{u}) ⊗ join K Δ[0] ⟶ X)
    (h : IsColimitCone (colimitPrismEndpoint G 1)) :
    IsColimitCone (colimitPrismTotalCocone G) := by
  have : Mono (prismEndpoint 1 K) := by unfold prismEndpoint; infer_instance
  apply (isColimitCone_iff_restrict_of_rightAnodyne _ _ (prismEndpoint_one_rightAnodyne K)).mpr
  rwa [colimitPrismTotalCocone_target]

end SerrePositivity.InfinityCategories.HomotopyLimits

module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeIsoFiberClass
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeTotalModelFiberPath

/-!
概要：元の模型比較に用いた底固定円柱の同じ fiber 制限と指定類を保持する。
方針：元の相対可換同型の同じ代表辺を fiber Hom へ写す。
規約：元の二三角形と全円柱を保持。使われ方：模型の全 path と各点の錐の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "e" => coherentCospanConeRelativePathIso F X Y Z C

/-- 模型の元の底固定円柱を同じ fiber 間の全円柱へ制限する。 -/
def coherentCospanConeFiberPathHomotopy :=
  relativeIsoFiberHomotopy p a
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection])
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection]) e b

/-- fiber 円柱を元へ含めると模型の元の全円柱の同じ始域制限。 -/
lemma coherentCospanConeFiberPathHomotopy_h_ι :
    (coherentCospanConeFiberPathHomotopy F X Y Z C b).h ≫ vertexFiberι p b =
      (vertexFiberι a b ▷ (Δ[1] : SSet.{u})) ≫
        (coherentCospanConeRelativePathHomotopy F X Y Z C).h :=
  relativeIsoFiberHomotopy_h_ι p a _ _ e b

/-- 模型の底固定円柱の fiber 制限の類は同じ指定相対可換同型の fiber 像。 -/
lemma coherentCospanConeFiberPathHomotopy_hom :
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentCospanConeFiberPathHomotopy F X Y Z C b)) =
    (relativeIsoFiberImage p a
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection])
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection]) e b).hom :=
  relativeIsoFiberHomotopy_hom p a _ _ e b

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantUnstraighteningValuePost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyRelativePost

/-!
概要：定値標的の元の値射影を、明示した頂点等式に沿って同じ固定値へ写す。
方針：元の射影の標的表示だけを、値対象の等式で移す。
規約：全係数と指定頂点等式を保持。使われ方：元の五因子式を同じ値空間で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値標的の射影を、同じ頂点等式で指定した値空間へ写す全族の射。 -/
def constantTargetValueProjectionTo {B C : SSet.{u + 1}} (p : C ⟶ B)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) p ⟶
      (ihom C).obj ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj) := by
  subst z'
  exact (constantUnstraighteningRelativeIso p z).hom ≫
    (ihom C).map (pointedSpaceFiberValueEquivalence z).hom

/-- 同じ定値標的への元の円柱の後合成は、指定値空間への全射影でも厳密に一致する。 -/
lemma functorHomotopyConstantPost_value_retarget {B C : SSet.{u + 1}}
    {J : B ⟶ SpaceInfinity.{u}} {z z' : SpaceInfinity.{u} _⦋0⦌}
    (H : SSet.Homotopy J (SSet.const z)) (H' : SSet.Homotopy J (SSet.const z'))
    (hz : z = z') (hh : H.h = H'.h) (p : C ⟶ B) :
    functorHomotopyRelativePost H p ≫ constantTargetValueProjectionTo p hz =
    functorHomotopyRelativePost H' p ≫ ((constantUnstraighteningRelativeIso p z').hom ≫
      (ihom C).map (pointedSpaceFiberValueEquivalence z').hom) := by
  subst z'
  have hH : H = H' := SSet.RelativeMorphism.Homotopy.ext hh
  subst H'
  rfl

/-- 同じ円柱の固定値への作用は、元の実全空間射・fiber 射影の後合成そのもの。 -/
lemma functorHomotopyConstantPost_value_retarget_action {B C : SSet.{u + 1}}
    {J : B ⟶ SpaceInfinity.{u}} {z z' : SpaceInfinity.{u} _⦋0⦌}
    (H : SSet.Homotopy J (SSet.const z)) (H' : SSet.Homotopy J (SSet.const z'))
    (hz : z = z') (hh : H.h = H'.h) (p : C ⟶ B) :
    functorHomotopyRelativePost H p ≫ constantTargetValueProjectionTo p hz =
    vertexFiberι ((ihom C).map (leftUnstraighteningProjection J)) (functorVertex p) ≫
      (ihom C).map ((leftUnstraighteningMappingVertexMap J (SSet.const z')
        (coherentVertexOfHomotopy H')).val ≫ constantUnstraighteningFiberProjection B z' ≫
          (pointedSpaceFiberValueEquivalence z').hom) := by
  exact (functorHomotopyConstantPost_value_retarget H H' hz hh p).trans
    (constantUnstraighteningRelativeIso_value_post (leftUnstraighteningProjection J) p z' _ _)

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePostThreeEdges
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の指定三角形比較を、元の二つの native 後合成の厳密な合成へ表示する。
方針：相対後合成の合成則で標的だけを揃え、同じ元の成分と三辺による表示を保持する。
規約：元の指定値を保持。使われ方：四面の式のホモトピー圏上での相殺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B)
local notation "va" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "vb" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "vc" => leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)
local notation "Pa" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection G) (Subtype.val va) (Subtype.property va) p
local notation "Pb" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J) (Subtype.val vb) (Subtype.property vb) p
local notation "Pc" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection J) (Subtype.val vc) (Subtype.property vc) p
local notation "hp" => relativeFunctorPost_comp (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection G) (leftUnstraighteningProjection J)
  (Subtype.val va) (Subtype.property va) (Subtype.val vb) (Subtype.property vb) p

/-- 元の同じ三角形比較の標的を、同じ二つの native 後合成の合成へ厳密に揃える。 -/
def functorTriangleSequentialPostComparison : FunctorIso Pc (Pa ≫ Pb) :=
  functorIsoOfEq (functorTrianglePostComparison T p) rfl (hp).symm

/-- 元の sequential 表示の成分は、元の後合成の比較の同じ指定成分を保持する。 -/
lemma functorTriangleSequentialPostComparison_app_heq_post
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq ((functorTriangleSequentialPostComparison T p).app x)
      ((functorTrianglePostComparison T p).app x) :=
  functorIso_app_heq_of_heq (functorTriangleSequentialPostComparison T p)
    (functorTrianglePostComparison T p) rfl hp (functorIsoOfEq_heq _ rfl (hp).symm) x

/-- 表示変更後の成分も、元の全実三辺の同じ指定比較による合成の値を保つ。 -/
lemma FunctorTrianglePointedWitness.sequentialPostComparison_app_heq_threeEdges
    {s : C ⟶ leftUnstraightening F} (w : FunctorTrianglePointedWitness T p s)
    (hi : s ≫ leftUnstraighteningProjection F = p) :
    HEq ((functorTriangleSequentialPostComparison T p).app
      (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi))
      (functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
          w.firstInverseNativeComparison hi)) := by
  have he := functorIso_app_heq_of_heq (functorTriangleSequentialPostComparison T p)
    (functorTrianglePostComparison T p) rfl hp
    (functorIsoOfEq_heq _ rfl (hp).symm)
    (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi)
  exact he.trans (w.postComparison_app_heq_threeEdges hi)

end SerrePositivity.InfinityCategories.F2

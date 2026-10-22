module

public import SerrePositivity.InfinityCategories.F2.RelativeFunctorPostIsoEvaluation
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLongWitness

/-!
概要：元の指定三角形比較を、全相対始域の後合成の関手同型として保持する。
方針：同じ相対頂点同型を豊穣後合成で送り、その成分を元の前合成へ値まで戻す。
規約：元の指定比較を再選択しない。使われ方：四面の比較の共通始点での自然性。
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
local notation "V" => coherentTriangleOfFunctorTriangle T
local notation "v₀₁" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "v₁₂" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "v₀₂" => leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)
local notation "θ" => unstraighteningTriangleRelativeVertexIso F G J
  (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle T))
local notation "hc" => Eq.trans (Category.assoc (Subtype.val v₀₁) (Subtype.val v₁₂)
  (leftUnstraighteningProjection J)) (Eq.trans
    (congrArg (fun f => Subtype.val v₀₁ ≫ f) (Subtype.property v₁₂)) (Subtype.property v₀₁))
local notation "Pf" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection J) (Subtype.val v₀₂) (Subtype.property v₀₂) p
local notation "Pg" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection J) (Subtype.val v₀₁ ≫ Subtype.val v₁₂) hc p

/-- 元の指定三角形比較を、全相対始域を動かす元の後合成の関手同型へ移す。 -/
def functorTrianglePostComparison : FunctorIso Pf Pg :=
  relativeFunctorPostVertexIso p (leftUnstraighteningProjection F) (leftUnstraighteningProjection J)
    (v₀₂).val ((v₀₁).val ≫ (v₁₂).val) (v₀₂).property hc θ

/-- 元の三角形の指定比較は、全相対始域空間上の同じ比較に対して自然。 -/
lemma functorTrianglePostComparison_naturality
    {x y : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌}
    (e : VertexIso x y) :
    VertexIso.map e Pf ≪≫ (functorTrianglePostComparison T p).app y =
      (functorTrianglePostComparison T p).app x ≪≫ VertexIso.map e Pg := by
  apply Iso.ext
  exact (functorTrianglePostComparison T p).toNatIso.hom.naturality e.hom

/-- 後合成の比較の成分は、元の指定三角形比較の同じ実始域射での前合成の値。 -/
lemma functorTrianglePostComparison_app_heq_pre
    (s : C ⟶ leftUnstraightening F) (hs : s ≫ leftUnstraighteningProjection F = p) :
    HEq ((functorTrianglePostComparison T p).app
      (relativeFunctorVertex (leftUnstraighteningProjection F) p s hs))
      (VertexIso.map θ
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          s)) :=
  relativeFunctorPostVertexIso_app_heq_pre p (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection J) (v₀₂).val ((v₀₁).val ≫ (v₁₂).val)
    (v₀₂).property hc θ s hs

end SerrePositivity.InfinityCategories.F2

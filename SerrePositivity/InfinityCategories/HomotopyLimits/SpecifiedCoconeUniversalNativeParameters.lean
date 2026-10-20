module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomPresentationTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeSpanUniversalHomDiagrams
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeSpanUniversalPathFamily

/-!
概要：元の指定余錐と native strict span の普遍全 Hom のパラメータ・点図式表示を揃える。
方針：同じ頂点の厳密な等式を使い、base 同型との移送の両立を適用する。
規約：元の頂点等式と同じ全 Hom を保持。使われ方：同じ終端係数上での全族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "s" => partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "q" => sliceUnderProjection p
local notation "r" => sliceUnderProjection (strictCoherentDiagram
  (partialColimitApexSpan c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "h" => specifiedPathCocone_vertex_eq_strictSpan hp p c hc dB dC

/-- 同じ実際の頂点の等式から、元の全 Hom のパラメータを native 側へ移す。 -/
def specifiedCoconeUniversalNativeParameter :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ pinchedHomLeft (JoinCocone.vertex s) y :=
  eqToHom (congrArg (fun z ↦ pinchedHomLeft z y) h)

/-- 元の指定余錐と strict span の点図式表示も、同じ頂点等式で厳密に一致する。 -/
lemma specifiedCoconeUniversalNativePointDiagram : coconeVertexDiagram d = coconeVertexDiagram s :=
  coconeVertexDiagram_of_vertex_eq d s h

/-- パラメータの移送と、同じ全 Hom の点図式表示への base 同型の逆は可換。 -/
lemma specifiedCoconeUniversalNativeParameter_terminal :
    specifiedCoconeUniversalNativeParameter hp p c hc dB dC y ≫
        (leftFibrationInitialBaseIso r s y).inv =
      (leftFibrationInitialBaseIso q d y).inv ≫
        eqToHom (congrArg (fun a ↦ coconeMappingSpace a y)
          (specifiedCoconeUniversalNativePointDiagram hp p c hc dB dC)) :=
  initialBaseIso_inv_vertexTransport q r d s h y

end
end SerrePositivity.InfinityCategories.HomotopyLimits

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeSpanUniversalRootShape
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomDiagramRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeUniversalFaces

/-!
概要：左右の native 普遍全図式族の根辺制限を、同じ全余錐族の同じ脚の族へ戻す。
方針：元の join 形状の厳密な一致と、普遍全族の二段制限の式を使う。
規約：共通パラメータと選択済みの全 Hom 族を保持。使われ方：元の左右の根辺比較の合流。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
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
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "σL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "σR" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
  (SSet.Edge.CompStruct.simplex (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "rfL" => specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "rfR" => specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "U" => specifiedCoconeUniversalNativeParameter hp p c hc dB dC y
local notation "L" => specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y
local notation "R" => specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y

/-- 同じ native 全余錐の共通脚の形状は、元の共通根辺図式を厳密に切り出す。 -/
lemma specifiedCoconeUniversalRootShape_diagram :
    (stdSimplex.δ (1 : Fin 3) ≫ nativeSpanLeftTriangleShape) ≫ Subtype.val s = root :=
  (Category.assoc _ _ _).trans
    ((congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·)
      (nativeSpanLeftHomDiagram_shape hp p c hc dB dC)).trans rfL)

/-- 同じ選択済み全 Hom 族を、左右で共通する同じ実際の脚へ制限した族。 -/
def specifiedCoconeUniversalCommonRootFamily :
    pinchedHomLeft (JoinCocone.vertex d) y ⟶ coconeMappingSpace root y :=
  U ≫ coconePointHomDiagramFiberFamily s
    (stdSimplex.δ (1 : Fin 3) ≫ nativeSpanLeftTriangleShape) root
    (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y

/-- 左の普遍全図式族の根辺は、同じ全余錐から得た共通脚の族そのもの。 -/
lemma specifiedCoconeLeftUniversalNativeFamily_root :
    L ≫ normalizedCoconeRestrictionFiber σL (stdSimplex.δ (1 : Fin 3)) rfL y =
      specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y := by
  exact (Category.assoc U (nativeSpanLeftUniversalHomDiagramFamily hp p c hc dB dC y)
    (normalizedCoconeRestrictionFiber σL (stdSimplex.δ (1 : Fin 3)) rfL y)).trans
      (congrArg (U ≫ ·) (coconePointHomDiagramFiberFamily_restrict s
        nativeSpanLeftTriangleShape σL (nativeSpanLeftHomDiagram_shape hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 3)) root rfL
        (stdSimplex.δ (1 : Fin 3) ≫ nativeSpanLeftTriangleShape) rfl
        (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y))

/-- 右の退化四面体の辺03も、同じ全余錐から得た同じ共通脚の族そのもの。 -/
lemma specifiedCoconeRightUniversalNativeFamily_root :
    R ≫ normalizedCoconeRestrictionFiber σR tetrahedronRootEdge rfR y =
      specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y := by
  exact (Category.assoc U (nativeSpanRightUniversalHomDiagramFamily hp p c hc dB dC y)
    (normalizedCoconeRestrictionFiber σR tetrahedronRootEdge rfR y)).trans
      (congrArg (U ≫ ·) (coconePointHomDiagramFiberFamily_restrict s
        nativeSpanRightTetrahedronShape σR (nativeSpanRightHomDiagram_shape hp p c hc dB dC)
        tetrahedronRootEdge root rfR
        (stdSimplex.δ (1 : Fin 3) ≫ nativeSpanLeftTriangleShape)
        nativeSpanUniversalRootShape_eq.symm
        (specifiedCoconeUniversalRootShape_diagram hp p c hc dB dC) y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits

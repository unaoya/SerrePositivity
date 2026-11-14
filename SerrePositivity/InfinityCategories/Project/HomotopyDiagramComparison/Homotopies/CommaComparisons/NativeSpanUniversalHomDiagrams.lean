module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeLegTriangleShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomDiagramFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.PartialColimitSpanTriangles

/-!
概要：元の native 普遍 span の全 Hom を、同じ左二単体・右退化四面体の全族へ制限する。
方針：strict nerve の元の射と join 形状を使い、全余錐族と同じ終端係数を保持する。
規約：選択済みの全 Hom 持ち上げを保持。使われ方：元の rooted 全族との終端固定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 元の native span の左射と余錐頂点が定める、同じ二単体の join 形状。 -/
def nativeSpanLeftTriangleShape : (Δ[2] : SSet.{u + 1}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingSpan))) Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape (AsSmall.up.map WalkingSpan.Hom.fst)

/-- 元の native span の右射の二単体に、同じ σ2 退化を施した join 形状。 -/
def nativeSpanRightTetrahedronShape : (Δ[3] : SSet.{u + 1}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingSpan))) Δ[0] :=
  stdSimplex.σ (2 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape (AsSmall.up.map WalkingSpan.Hom.snd)

/-- 左の同じ join 形状の最後の頂点は、元の native 余錐頂点の右包含である。 -/
lemma nativeSpanLeftTriangleShape_tip :
    (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
        nativeSpanLeftTriangleShape.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (AsSmall.{u} WalkingSpan))) Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape_tip (AsSmall.up.map WalkingSpan.Hom.fst)

/-- 右の同じ退化四面体の最後の頂点も、元の native 余錐頂点の右包含である。 -/
lemma nativeSpanRightTetrahedronShape_tip :
    ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫ stdSimplex.δ (0 : Fin 4)) ≫
        nativeSpanRightTetrahedronShape.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (AsSmall.{u} WalkingSpan))) Δ[0] := by
  have hv : (((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
      stdSimplex.δ (0 : Fin 4)) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[3]) ≫
      stdSimplex.σ (2 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [nativeSpanRightTetrahedronShape, ← Category.assoc, hv]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape_tip (AsSmall.up.map WalkingSpan.Hom.snd)

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)

/-- 左の同じ join 形状は、元の指定した native 合成図式そのものを切り出す。 -/
lemma nativeSpanLeftHomDiagram_shape : nativeSpanLeftTriangleShape ≫ Subtype.val d = σ := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape_diagram (AsSmall.up.map WalkingSpan.Hom.fst) F d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object c.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dB.vertex)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc f (i ≫ p) rfl dB))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom_edge c hc f (i ≫ p) rfl dB).symm

/-- 左の元の native 図式の終端は、同じ元の strict 余錐頂点の図式である。 -/
lemma nativeSpanLeftHomDiagram_tip : v ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d :=
  (congrArg (v ≫ ·) (nativeSpanLeftHomDiagram_shape hp p c hc dB dC).symm).trans
    ((Category.assoc v nativeSpanLeftTriangleShape (Subtype.val d)).symm.trans
      ((congrArg (· ≫ Subtype.val d) nativeSpanLeftTriangleShape_tip).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_inr d)))

/-- 元の native 普遍余錐の全 Hom による、同じ左の合成図式上の実際の全族。 -/
def nativeSpanLeftUniversalHomDiagramFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily d nativeSpanLeftTriangleShape σ
    (nativeSpanLeftHomDiagram_shape hp p c hc dB dC) y

/-- 同じ native 全族の終端係数は、元の選択済みの普遍全 Hom の点図式表示そのもの。 -/
lemma nativeSpanLeftUniversalHomDiagramFamily_terminal :
    nativeSpanLeftUniversalHomDiagramFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v (nativeSpanLeftHomDiagram_tip hp p c hc dB dC) y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d y).inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_terminal d nativeSpanLeftTriangleShape σ
    (nativeSpanLeftHomDiagram_shape hp p c hc dB dC) y v nativeSpanLeftTriangleShape_tip
    (nativeSpanLeftHomDiagram_tip hp p c hc dB dC)
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)

/-- 右の同じ join 形状は、元の指定した native 合成図式そのものを切り出す。 -/
lemma nativeSpanRightHomDiagram_shape : nativeSpanRightTetrahedronShape ≫ Subtype.val d = σ := by
  change (stdSimplex.σ (2 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape (AsSmall.up.map WalkingSpan.Hom.snd)) ≫ Subtype.val d = σ
  rw [Category.assoc]
  apply congrArg (stdSimplex.σ (2 : Fin 3) ≫ ·)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeLegTriangleShape_diagram (AsSmall.up.map WalkingSpan.Hom.snd) F d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object c.vertex) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object dC.vertex)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc g (j ≫ p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom_edge c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).symm

/-- 右の元の native 図式の終端は、同じ元の strict 余錐頂点の図式である。 -/
lemma nativeSpanRightHomDiagram_tip : v ≫ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d :=
  (congrArg (v ≫ ·) (nativeSpanRightHomDiagram_shape hp p c hc dB dC).symm).trans
    ((Category.assoc v nativeSpanRightTetrahedronShape (Subtype.val d)).symm.trans
      ((congrArg (· ≫ Subtype.val d) nativeSpanRightTetrahedronShape_tip).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_inr d)))

/-- 元の native 普遍余錐の全 Hom による、同じ右の合成図式上の実際の全族。 -/
def nativeSpanRightUniversalHomDiagramFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily d nativeSpanRightTetrahedronShape σ
    (nativeSpanRightHomDiagram_shape hp p c hc dB dC) y

/-- 同じ native 全族の終端係数は、元の選択済みの普遍全 Hom の点図式表示そのもの。 -/
lemma nativeSpanRightUniversalHomDiagramFamily_terminal :
    nativeSpanRightUniversalHomDiagramFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ v (nativeSpanRightHomDiagram_tip hp p c hc dB dC) y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d y).inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomDiagramFiberFamily_terminal d nativeSpanRightTetrahedronShape σ
    (nativeSpanRightHomDiagram_shape hp p c hc dB dC) y v nativeSpanRightTetrahedronShape_tip
    (nativeSpanRightHomDiagram_tip hp p c hc dB dC)
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

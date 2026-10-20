module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeLegTriangleShape
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomDiagramFamily

/-!
概要：元の余錐の合成二単体全体に、同じ選択済みの普遍全 Hom の族を制限する。
方針：実際の join 形状と終端の式を、全余錐族の部分図式制限に適用する。
規約：元の二単体と同じ終端係数を保持。使われ方：native span の三角形全族との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p)
  {a b : K _⦋0⦌} (e : K.Edge a b) (y : X _⦋0⦌)
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)

/-- 元の図式の辺と余錐の脚の、同じ実際の合成二単体の図式。 -/
def coconeLegTriangleDiagram : (Δ[2] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm (coconeVertexLegCompStruct c e).simplex

omit [Quasicategory X] in
/-- 元の二単体の最後の頂点は、同じ元の余錐頂点図式である。 -/
lemma coconeLegTriangleDiagram_tip : v ≫ coconeLegTriangleDiagram c e = coconeVertexDiagram c :=
  (congrArg (v ≫ ·) (coconeLegTriangleShape_diagram e c).symm).trans
    ((Category.assoc v (coconeLegTriangleShape e) c.val).symm.trans
      ((congrArg (· ≫ c.val) (coconeLegTriangleShape_tip e)).trans
        (coconeVertexDiagram_inr c)))

/-- 元の実際の合成二単体の下にある、同じ選択済みの普遍全 Hom の族。 -/
def coconeLegTriangleHomFamily :
    pinchedHomLeft c.vertex y ⟶ sliceUnder (coconeLegTriangleDiagram c e) :=
  coconePointHomDiagramFamily c (coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (coconeLegTriangleShape_diagram e c) y

/-- 同じ普遍二単体族は、元の固定終点 y 上に留まる。 -/
lemma coconeLegTriangleHomFamily_fixed :
    coconeLegTriangleHomFamily c e y ≫ sliceUnderProjection (coconeLegTriangleDiagram c e) =
      SSet.const y :=
  coconePointHomDiagramFamily_fixed c (coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (coconeLegTriangleShape_diagram e c) y

/-- 元の普遍二単体族を、固定終点 fiber の族として保持する。 -/
def coconeLegTriangleHomFiberFamily :
    pinchedHomLeft c.vertex y ⟶ coconeMappingSpace (coconeLegTriangleDiagram c e) y :=
  coconePointHomDiagramFiberFamily c (coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (coconeLegTriangleShape_diagram e c) y

/-- 固定終点の包含後は、元の同じ普遍二単体族そのものである。 -/
lemma coconeLegTriangleHomFiberFamily_ι :
    coconeLegTriangleHomFiberFamily c e y ≫
        vertexFiberι (sliceUnderProjection (coconeLegTriangleDiagram c e)) y =
      coconeLegTriangleHomFamily c e y :=
  coconePointHomDiagramFiberFamily_ι c (coconeLegTriangleShape e) (coconeLegTriangleDiagram c e)
    (coconeLegTriangleShape_diagram e c) y

/-- 元の二単体の終端係数は、同じ普遍全 Hom の点図式表示に厳密に一致する。 -/
lemma coconeLegTriangleHomFiberFamily_terminal :
    coconeLegTriangleHomFiberFamily c e y ≫
        normalizedCoconeRestrictionFiber (coconeLegTriangleDiagram c e) v
          (coconeLegTriangleDiagram_tip c e) y =
      (leftFibrationInitialBaseIso (sliceUnderProjection p) c y).inv :=
  coconePointHomDiagramFiberFamily_terminal c (coconeLegTriangleShape e)
    (coconeLegTriangleDiagram c e) (coconeLegTriangleShape_diagram e c) y v
    (coconeLegTriangleShape_tip e) (coconeLegTriangleDiagram_tip c e)

end
end SerrePositivity.InfinityCategories.HomotopyLimits

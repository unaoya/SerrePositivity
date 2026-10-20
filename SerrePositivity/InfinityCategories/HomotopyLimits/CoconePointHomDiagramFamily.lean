module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointFullHomFamily
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedCosliceRestrictionComposition

/-!
概要：native な余錐全図式の部分図式に、元の全 Hom の同じ族を制限する。
方針：同じ全余錐族の正規化制限と二段制限の合成則で、元の終端係数を回収する。
規約：実際の形状埋め込みと終端の式を保持。使われ方：span の三角形・退化四面体の普遍族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K L X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p)
  (i : L ⟶ join K (Δ[0] : SSet.{u})) (s : L ⟶ X) (hs : i ≫ c.val = s) (y : X _⦋0⦌)
local notation "q" => sliceUnderProjection p

/-- 同じ元の全 Hom パラメータによる、余錐の実際の部分図式上の全族。 -/
def coconePointHomDiagramFamily : pinchedHomLeft c.vertex y ⟶ sliceUnder s :=
  coconePointFullHomFamily c y ≫ normalizedCoconeRestriction c.val i hs

/-- 部分図式に制限しても、元の同じ終点 y を全パラメータで保つ。 -/
lemma coconePointHomDiagramFamily_fixed :
    coconePointHomDiagramFamily c i s hs y ≫ sliceUnderProjection s = SSet.const y := by
  rw [coconePointHomDiagramFamily, Category.assoc, normalizedCoconeRestriction_projection,
    coconePointFullHomFamily_fixed]

/-- 同じ部分図式の族を、元の全余錐族の固定終点 fiber での制限として保持する。 -/
def coconePointHomDiagramFiberFamily : pinchedHomLeft c.vertex y ⟶ coconeMappingSpace s y :=
  coconePointFullHomFiberFamily c y ≫ normalizedCoconeRestrictionFiber c.val i hs y

/-- 固定終点 fiber の包含後は、元の同じ部分図式族そのものである。 -/
lemma coconePointHomDiagramFiberFamily_ι :
    coconePointHomDiagramFiberFamily c i s hs y ≫ vertexFiberι (sliceUnderProjection s) y =
      coconePointHomDiagramFamily c i s hs y := by
  simp only [coconePointHomDiagramFiberFamily, Category.assoc,
    normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  exact (Category.assoc (coconePointFullHomFiberFamily c y)
    (vertexFiberι (sliceUnderProjection c.val) y)
    (normalizedCoconeRestriction c.val i hs)).symm.trans
      (congrArg (· ≫ normalizedCoconeRestriction c.val i hs)
        (coconePointFullHomFiberFamily_ι c y))

variable (v : (Δ[0] : SSet.{u}) ⟶ L) (hv : v ≫ i = joinInr K Δ[0])
  (ht : v ≫ s = coconeVertexDiagram c)

include hv

/-- 同じ右端点を持つ部分図式族は、元の全 Hom の同じ点図式表示を終端係数に持つ。 -/
lemma coconePointHomDiagramFamily_terminal :
    coconePointHomDiagramFamily c i s hs y ≫ normalizedCoconeRestriction s v ht =
      (leftFibrationInitialBaseIso q c y).inv ≫
        vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y :=
  (normalizedCoconeRestriction_twoStep_family c.val i s hs v (coconeVertexDiagram c) ht
    (joinInr K Δ[0]) hv (coconeVertexDiagram_inr c) (coconePointFullHomFamily c y)).trans
      (coconePointFullHomFamily_terminal c y)

/-- 固定終点 fiber でも、元の普遍全 Hom の同じ終端係数を厳密に回収する。 -/
lemma coconePointHomDiagramFiberFamily_terminal :
    coconePointHomDiagramFiberFamily c i s hs y ≫
        normalizedCoconeRestrictionFiber s v ht y = (leftFibrationInitialBaseIso q c y).inv := by
  exact (Category.assoc (coconePointFullHomFiberFamily c y)
    (normalizedCoconeRestrictionFiber c.val i hs y)
    (normalizedCoconeRestrictionFiber s v ht y)).trans
      ((congrArg (coconePointFullHomFiberFamily c y ≫ ·)
        (normalizedCoconeRestrictionFiber_twoStep c.val i s hs v (coconeVertexDiagram c) ht
          (joinInr K Δ[0]) hv (coconeVertexDiagram_inr c) y)).trans
            (coconePointFullHomFiberFamily_terminal c y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits

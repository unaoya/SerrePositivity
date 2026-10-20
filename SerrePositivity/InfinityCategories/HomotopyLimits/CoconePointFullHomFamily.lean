module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeNestedCosliceProjection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomFamily

/-!
概要：元の全 Hom パラメータによる余錐族を、余錐全図式の下の同じ全族として保持する。
方針：始点固定 Hom の持ち上げを二重 coslice の同型の逆で戻す。
規約：元の選択した持ち上げを保持。使われ方：native 普遍 span の二単体族と終端の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p) (y : X _⦋0⦌)
local notation "q" => sliceUnderProjection p
local notation "d" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder p)) c
local notation "L" => leftFibrationPointHomLift q c y
local notation "ι" => vertexFiberι (sliceUnderProjection d ≫ q) y

/-- 元の選択した全 Hom の持ち上げを、余錐全図式の下の全族へ戻す。 -/
def coconePointFullHomFamily : pinchedHomLeft c.vertex y ⟶ sliceUnder c.val :=
  L ≫ ι ≫ (nestedCosliceIso c).inv
local notation "F" => coconePointFullHomFamily c y

/-- 元の図式への制限は、同じ既存の全 Hom による余錐族そのものである。 -/
lemma coconePointFullHomFamily_restriction :
    F ≫ colimitCosliceRestriction c = coconePointHomFamily c y ≫ vertexFiberι q y := by
  calc
    _ = (L ≫ ι) ≫ ((nestedCosliceIso c).inv ≫ colimitCosliceRestriction c) := by
      simp only [coconePointFullHomFamily, Category.assoc]
    _ = (L ≫ ι) ≫ sliceUnderProjection d :=
      congrArg ((L ≫ ι) ≫ ·) (coconeNestedCoslice_inv_restriction c)
    _ = _ := by
      simp only [coconePointHomFamily, leftFibrationPointHomFamily,
        leftFibrationInitialEvaluation, Category.assoc, vertexFiberMap_ι]

/-- 全余錐族の可変終点は、元の同じ余錐族の終点そのものである。 -/
lemma coconePointFullHomFamily_endpoint :
    F ≫ sliceUnderProjection c.val = coconePointHomFamily c y ≫ vertexFiberι q y ≫ q := by
  have h := congrArg (· ≫ q) (coconePointFullHomFamily_restriction c y)
  simpa only [Category.assoc, colimitCosliceRestriction_projection] using h

/-- 元の終点 y を、全余錐族の全パラメータで厳密に保持する。 -/
lemma coconePointFullHomFamily_fixed : F ≫ sliceUnderProjection c.val = SSet.const y := by
  rw [coconePointFullHomFamily_endpoint, vertexFiberι_comp, SSet.comp_const]

/-- 余錐全図式の右端点への制限は、元の全 Hom の点図式表示そのものである。 -/
lemma coconePointFullHomFamily_terminal :
    F ≫ normalizedCoconeRestriction c.val (joinInr K Δ[0]) (coconeVertexDiagram_inr c) =
      (leftFibrationInitialBaseIso q c y).inv ≫
        vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y := by
  have h := congrArg (· ≫ vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y)
    (leftFibrationPointHomLift_projection q c y)
  simp only [Category.assoc, leftFibrationInitialProjection] at h
  exact (coconeNestedCoslice_inv_terminal_family c (L ≫ ι)).trans h

/-- 同じ全余錐族を、固定終点 y の fiber の全族として表示する。 -/
def coconePointFullHomFiberFamily :
    pinchedHomLeft c.vertex y ⟶ coconeMappingSpace c.val y :=
  vertexFiberLift (sliceUnderProjection c.val) y F (coconePointFullHomFamily_fixed c y)

/-- 固定終点 fiber の包含後は、元の同じ全余錐族そのものである。 -/
lemma coconePointFullHomFiberFamily_ι :
    coconePointFullHomFiberFamily c y ≫ vertexFiberι (sliceUnderProjection c.val) y = F :=
  vertexFiberLift_ι _ _ _ _

/-- 全余錐族を元の図式へ制限すると、同じ既存の全 Hom の余錐族を厳密に回収する。 -/
lemma coconePointFullHomFiberFamily_restriction :
    coconePointFullHomFiberFamily c y ≫ normalizedCoconeRestrictionFiber c.val
        (joinInl K Δ[0]) c.property y = coconePointHomFamily c y := by
  apply vertexFiber_hom_ext q y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  calc
    _ = (coconePointFullHomFiberFamily c y ≫ vertexFiberι (sliceUnderProjection c.val) y) ≫
        normalizedCoconeRestriction c.val (joinInl K Δ[0]) c.property :=
      (Category.assoc _ _ _).symm
    _ = F ≫ normalizedCoconeRestriction c.val (joinInl K Δ[0]) c.property :=
      congrArg (· ≫ normalizedCoconeRestriction c.val (joinInl K Δ[0]) c.property)
        (coconePointFullHomFiberFamily_ι c y)
    _ = F ≫ colimitCosliceRestriction c :=
      congrArg (F ≫ ·) (coconeNestedCoslice_restriction c).symm
    _ = _ := coconePointFullHomFamily_restriction c y

/-- 固定終点でも、右端点は元の全 Hom の同じ点図式表示に厳密に一致する。 -/
lemma coconePointFullHomFiberFamily_terminal :
    coconePointFullHomFiberFamily c y ≫ normalizedCoconeRestrictionFiber c.val
        (joinInr K Δ[0]) (coconeVertexDiagram_inr c) y =
      (leftFibrationInitialBaseIso q c y).inv := by
  apply vertexFiber_hom_ext (sliceUnderProjection (coconeVertexDiagram c)) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  rw [← Category.assoc, coconePointFullHomFiberFamily_ι, coconePointFullHomFamily_terminal]

end
end SerrePositivity.InfinityCategories.HomotopyLimits

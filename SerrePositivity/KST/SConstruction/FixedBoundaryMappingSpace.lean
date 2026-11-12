module
public import SerrePositivity.KST.SConstruction.FamilyCylinderEndpointAdjustment
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-! # 元の全境界を固定した写像空間と実比較辺
概要：部分単体集合上の写像を厳密に固定する Kan 写像空間を構成する。
方針：内部 Hom の単射制限の頂点 fiber を取り、元の相対円柱を同じ実辺へ移す。
規約：固定条件は全境界・全時刻での実等号。標的の Kan 性だけを用いる。
使われ方：累積補正の両端固定比較を同じ相対写像空間内で合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 元の全境界を厳密に固定する写像の単体集合。 -/
def fixedBoundaryMappingSpace {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)

/-- 元の写像空間への包含。 -/
def fixedBoundaryMappingSpaceι {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E) :
    fixedBoundaryMappingSpace j b ⟶ (ihom T).obj E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)

/-- 単射な境界と Kan 標的に対する固定境界写像空間は Kan。 -/
instance fixedBoundaryMappingSpace_kanComplex {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] (b : A ⟶ E) : KanComplex (fixedBoundaryMappingSpace j b) := by
  rw [KanComplex.iff]
  intro n i fs hf
  let t := hf.desc
  let sq : CommSq (t ≫ fixedBoundaryMappingSpaceι j b) (horn (n + 1) i).ι
      ((pre j).app E) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)) := by
    constructor
    rw [Category.assoc, fixedBoundaryMappingSpaceι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, SSet.comp_const]
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ((pre j).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) sq.lift sq.fac_right
  have hl : (horn (n + 1) i).ι ≫ l = t := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre j).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact sq.fac_left
  refine ⟨l, fun k hk => ?_⟩
  rw [← horn.ι_ι_assoc i k hk, hl]
  exact hf.ι_desc k hk

/-- 指定した全境界を持つ元の写像の頂点。 -/
def fixedBoundaryMappingVertex {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    (f : T ⟶ E) (hf : j ≫ f = b) : (fixedBoundaryMappingSpace j b) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) 0
    rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]⟩

/-- 元の相対円柱の curry は、境界の同じ頂点に全時刻で定数。 -/
lemma fixedBoundaryHomotopy_curry {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    curry H.h ≫ (pre j).app E = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  exact hr

/-- 元の相対円柱全体を固定境界写像空間の同じ区間へ移す。 -/
def fixedBoundaryMappingPath {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    (Δ[1] : SSet.{u}) ⟶ fixedBoundaryMappingSpace j b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ((pre j).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) (curry H.h)
    (fixedBoundaryHomotopy_curry j b H hr)

/-- 同じ円柱を元の写像空間へ戻すと全 curry そのもの。 -/
lemma fixedBoundaryMappingPath_ι {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    fixedBoundaryMappingPath j b H hr ≫ fixedBoundaryMappingSpaceι j b = curry H.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 元の両端頂点を持つ、固定境界空間内の同じ実比較辺。 -/
def fixedBoundaryMappingEdge {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (hf : j ≫ f = b) (hg : j ≫ g = b) (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    (fixedBoundaryMappingSpace j b).Edge
      (fixedBoundaryMappingVertex j b f hf) (fixedBoundaryMappingVertex j b g hg) where
  edge := SSet.yonedaEquiv (fixedBoundaryMappingPath j b H hr)
  src_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).src_eq
  tgt_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).tgt_eq

end SerrePositivity.KST.SConstruction

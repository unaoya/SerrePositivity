module
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifier
public import SerrePositivity.InfinityCategories.Stable.LoopCospanRepresentation
public import SerrePositivity.InfinityCategories.Stable.LimitConeTerminalComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedEndpointConeSpace

/-!
概要：元の loop 比較を固定 cospan の錐圏へ持ち上げ、同じ実区間族の同値性を得る。
方針：元の全単体と比較円柱を保ち、厳密 fiber の普遍性で接続する。
規約：安定性を先取りしない。使われ方：一般安定性判定の実 loop fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の loop 図式の普遍錐の頂点値は、同じ四角形の pullback 錐。 -/
lemma loopDiagramConeFamily_vertex {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    ((loopDiagramConeFamily X ≫
      (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι).app
        (Opposite.op ⦋0⦌) t.diagramVertex) = functorVertex (pullbackCone t.square).val := by
  rw [loopDiagramConeFamily_ι]
  rfl

/-- 元の loop 図式の底の頂点値は、同じ四角形の実 cospan。 -/
lemma loopDiagramConeFamily_base_vertex {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    ((loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X).app
      (Opposite.op ⦋0⦌) t.diagramVertex) = functorVertex (pullbackCospan t.square) := by
  change (coneRestriction (horn 2 2 : SSet.{u}) X).app (Opposite.op ⦋0⦌)
    ((loopDiagramConeFamily X ≫
      (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι).app
        (Opposite.op ⦋0⦌) t.diagramVertex) = _
  rw [loopDiagramConeFamily_vertex]
  change functorVertex (joinInr Δ[0] (horn 2 2 : SSet.{u}) ≫
    (pullbackCone t.square).val) = _
  rw [(pullbackCone t.square).property]

/-- 固定頂点からの同じ実 cospan の全錐を、元の loop 錐全体へ戻す。 -/
def loopConeFixedApexLift {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ⟶ loopConeObjects X :=
  pullback.lift (HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x)
    (SSet.const t.diagramVertex) (by
      change HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x ≫
        (pre (joinInr (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).app X =
        SSet.const t.diagramVertex ≫
          (loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X)
      rw [HomotopyLimits.fixedApexConeFamilyEvaluation_inr, SSet.const_comp,
        loopDiagramConeFamily_base_vertex])

/-- 固定頂点からの実 lift は、元の全錐への評価を回収する。 -/
lemma loopConeFixedApexLift_diagram {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    loopConeFixedApexLift t x ≫ loopConeObjectDiagram X =
      HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x :=
  pullback.lift_fst _ _ _

/-- 固定頂点からの実 lift の loop 図式は、元の指定四角形に厳密に定値。 -/
lemma loopConeFixedApexLift_loop {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    loopConeFixedApexLift t x ≫ loopConeObjectLoop X = SSet.const t.diagramVertex :=
  pullback.lift_snd _ _ _

/-- 元の loop 比較を、同じ実 cospan の固定頂点の全錐へ制限する。 -/
def loopConeFixedApexComparisonHomotopy {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    SSet.Homotopy (HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x)
      (SSet.const (functorVertex (pullbackCone t.square).val)) where
  h := (loopConeFixedApexLift t x ▷ (Δ[1] : SSet.{u})) ≫ (loopConeComparisonHomotopy X).h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, (loopConeComparisonHomotopy X).h₀,
      loopConeFixedApexLift_diagram]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, (loopConeComparisonHomotopy X).h₁]
    rw [← Category.assoc (loopConeFixedApexLift t x) (loopConeObjectLoop X),
      loopConeFixedApexLift_loop, SSet.const_comp, loopDiagramConeFamily_vertex]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 制限した元の loop 比較は、底の図式を全時刻で厳密に固定する。 -/
lemma loopConeFixedApexComparisonHomotopy_over {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexComparisonHomotopy t x).h ≫ coneRestriction (horn 2 2 : SSet.{u}) X =
      SSet.const (functorVertex (pullbackCospan t.square)) := by
  let A := HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x
  let r := loopConeFixedApexLift t x
  change (r ▷ (Δ[1] : SSet.{u})) ≫ ((loopConeComparisonHomotopy X).h ≫
    coneRestriction (horn 2 2 : SSet.{u}) X) = _
  rw [loopConeComparisonHomotopy_over]
  rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  rw [← Category.assoc r (loopConeObjectDiagram X), loopConeFixedApexLift_diagram]
  change fst A (Δ[1] : SSet.{u}) ≫
    (HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).app X) = _
  rw [HomotopyLimits.fixedApexConeFamilyEvaluation_inr, SSet.comp_const]

/-- 元の loop 比較を、同じ固定 cospan の錐圏への実ホモトピーへ持ち上げる。 -/
def loopConeFixedApexComparison {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    SSet.Homotopy (vertexFiberι (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x)
      (SSet.const ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))) where
  h := vertexFiberLift (coneRestriction (horn 2 2 : SSet.{u}) X)
    (functorVertex (pullbackCospan t.square)) (loopConeFixedApexComparisonHomotopy t x).h
      (loopConeFixedApexComparisonHomotopy_over t x)
  h₀ := by
    apply vertexFiber_hom_ext (coneRestriction (horn 2 2 : SSet.{u}) X)
      (functorVertex (pullbackCospan t.square))
    rw [Category.assoc, vertexFiberLift_ι, (loopConeFixedApexComparisonHomotopy t x).h₀]
    rfl
  h₁ := by
    apply vertexFiber_hom_ext (coneRestriction (horn 2 2 : SSet.{u}) X)
      (functorVertex (pullbackCospan t.square))
    rw [Category.assoc, vertexFiberLift_ι, (loopConeFixedApexComparisonHomotopy t x).h₁]
    change SSet.const (functorVertex (pullbackCone t.square).val) =
      SSet.const ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square)) ≫
          vertexFiberι (coneRestriction (horn 2 2 : SSet.{u}) X)
            (functorVertex (pullbackCospan t.square))
    rw [SSet.const_comp, sliceConeFamilyMap_app_zero]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 錐圏へ持ち上げた比較は、元の同じ loop 比較の円柱を回収する。 -/
lemma loopConeFixedApexComparison_ι {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexComparison t x).h ≫
      vertexFiberι (coneRestriction (horn 2 2 : SSet.{u}) X)
        (functorVertex (pullbackCospan t.square)) =
      (loopConeFixedApexLift t x ▷ (Δ[1] : SSet.{u})) ≫ (loopConeComparisonHomotopy X).h :=
  rfl

/-- 錐圏へ持ち上げた元の loop 比較の、同じ実区間族は同値。 -/
lemma loopConeFixedApexComparison_interval_isQCatEquivalence {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    IsQCatEquivalence (terminalComparisonIntervalFamily
      (HomotopyLimits.coneFamilyApex (pullbackCospan t.square))
      ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square)) x
      (vertexFiberι (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x)
      (vertexFiberι_comp (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x)
      (loopConeFixedApexComparison t x)) :=
  limitConeTerminalComparison_isQCatEquivalence (pullbackCospan t.square)
    (pullbackCone t.square) t.isPullback x (loopConeFixedApexComparison t x)
end SerrePositivity.InfinityCategories

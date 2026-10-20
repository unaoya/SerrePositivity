module

public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportMapping
public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingEvaluation
public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingVertices
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianScaffold

/-!
概要：水平辺を cocartesian 辺へ送る scaffold 上の相対関手空間と実際の評価を構成する。
方針：相対 Hom の全部分複体に水平辺の条件を課し、strict な変換の全評価を持ち上げる。
規約：高次の相対自然変換は全て保つ。scaffold の全空間に quasicategory 性は要求しない。
使われ方：cocartesian strict transport の写像空間比較を scaffold 制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 相対関手の元の射が replacement の全ての水平辺を cocartesian に送る条件。 -/
def CocartesianScaffoldFunctorPredicate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C)
    (v : (relativeFunctorSpace q (simplicialReplacementProjection F)) _⦋0⦌) : Prop :=
  ∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌), IsCocartesianEdge q
    ((((relativeFunctorVertexEquiv q (simplicialReplacementProjection F)).symm v).val).app
      (Opposite.op ⦋1⦌) (kanScaffoldHorizontalEdge F f x))

/-- 元の相対関手の頂点で、水平辺の条件を実際の射の条件として回収する。 -/
lemma cocartesianScaffoldFunctorPredicate_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C)
    (l : simplicialReplacement F ⟶ D) (hl : l ≫ q = simplicialReplacementProjection F) :
    CocartesianScaffoldFunctorPredicate F q
      (relativeFunctorVertex q (simplicialReplacementProjection F) l hl) ↔
      ∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌),
        IsCocartesianEdge q (l.app (Opposite.op ⦋1⦌) (kanScaffoldHorizontalEdge F f x)) := by
  change (∀ {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌), IsCocartesianEdge q
    ((((relativeFunctorVertexEquiv q (simplicialReplacementProjection F)).symm
      ((relativeFunctorVertexEquiv q (simplicialReplacementProjection F)) ⟨l, hl⟩)).val).app _
        (kanScaffoldHorizontalEdge F f x))) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 全ての水平辺を cocartesian に送る相対関手が張る全部分複体。 -/
def CocartesianScaffoldFunctorSpace {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) : SSet.{u} :=
  fullSubcomplexOnVertices (relativeFunctorSpace q (simplicialReplacementProjection F))
    (CocartesianScaffoldFunctorPredicate F q)

/-- 標的の射影が inner fibration なら水平辺を保つ相対関手空間は quasicategory。 -/
instance cocartesianScaffoldFunctorSpace_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) [InnerFibration q] :
    Quasicategory (CocartesianScaffoldFunctorSpace F q) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- 水平辺を保つ相対関手空間から元の全相対関手空間への包含。 -/
def cocartesianScaffoldFunctorInclusion {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    CocartesianScaffoldFunctorSpace F q ⟶
      relativeFunctorSpace q (simplicialReplacementProjection F) :=
  (fullSubcomplexOnVertices _ (CocartesianScaffoldFunctorPredicate F q)).ι

/-- 水平辺を保つ相対関手空間の包含は単射。 -/
instance cocartesianScaffoldFunctorInclusion_mono {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    Mono (cocartesianScaffoldFunctorInclusion F q) :=
  inferInstanceAs (Mono (fullSubcomplexOnVertices _ (CocartesianScaffoldFunctorPredicate F q)).ι)

/-- cocartesian strict transport への全変換を universal scaffold で評価する元の相対射。 -/
def cocartesianDiagramScaffoldRawMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    strictDiagramMappingSpace F (kanCocartesianStrictTransportDiagram q) ⟶
      relativeFunctorSpace q (simplicialReplacementProjection F) :=
  relativeFunctorCurry
    (strictDiagramMappingReplacementEvaluation F (kanCocartesianStrictTransportDiagram q) ≫
      kanUniversalScaffold q) (by
        rw [Category.assoc, kanUniversalScaffold_projection,
          strictDiagramMappingReplacementEvaluation_projection])

/-- 全評価の頂点は元の自然変換の replacement の射に universal scaffold を合成したもの。 -/
lemma cocartesianDiagramScaffoldRawMap_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C)
    (η : F ⟶ kanCocartesianStrictTransportDiagram q) :
    (cocartesianDiagramScaffoldRawMap F q).app (Opposite.op ⦋0⦌)
      (strictDiagramMappingVertex η) =
      relativeFunctorVertex q (simplicialReplacementProjection F)
        (simplicialReplacementMap η ≫ kanUniversalScaffold q) (by
          rw [Category.assoc, kanUniversalScaffold_projection,
            simplicialReplacementMap_projection]) := by
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 元の strict な自然変換の scaffold 評価は全水平辺を cocartesian に送る。 -/
lemma cocartesianDiagramScaffoldRawMap_vertex_horizontal {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C)
    (η : F ⟶ kanCocartesianStrictTransportDiagram q) :
    CocartesianScaffoldFunctorPredicate F q
      ((cocartesianDiagramScaffoldRawMap F q).app (Opposite.op ⦋0⦌)
        (strictDiagramMappingVertex η)) := by
  rw [cocartesianDiagramScaffoldRawMap_vertex, cocartesianScaffoldFunctorPredicate_vertex]
  intro c d f x
  have h : (simplicialReplacementMap η).app (Opposite.op ⦋1⦌)
      (kanScaffoldHorizontalEdge F f x) =
      kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram q) f ((η.app c).app _ x) := by
    change (⟨ComposableArrows.mk₁ f, SSet.const x ≫ η.app c⟩ :
      simplicialReplacementSimplex (kanCocartesianStrictTransportDiagram q) 1) = _
    rw [SSet.const_comp]
    rfl
  change IsCocartesianEdge q ((kanUniversalScaffold q).app _
    ((simplicialReplacementMap η).app _ (kanScaffoldHorizontalEdge F f x)))
  rw [h]
  exact kanUniversalScaffold_horizontal q f _

/-- 全パラメーターの scaffold 評価を、水平辺を保つ実際の相対関手空間へ制限する。 -/
def cocartesianDiagramScaffoldMappingSpaceMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    strictDiagramMappingSpace F (kanCocartesianStrictTransportDiagram q) ⟶
      CocartesianScaffoldFunctorSpace F q :=
  fullSubcomplexLift _ (cocartesianDiagramScaffoldRawMap F q) (by
    intro v
    obtain ⟨η, rfl⟩ := exists_strictDiagramMappingVertex F _ v
    exact cocartesianDiagramScaffoldRawMap_vertex_horizontal F q η)

end SerrePositivity.InfinityCategories

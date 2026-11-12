module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHomPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationVertex

/-!
概要：定値図式間の全変換空間を、元の二頂点間の区間写像のパラメータ族へ転置する。
方針：元の全 prism の因子を結合し直し、同じ両端条件で区間へ curry する。
規約：全てのパラメータと高次単体を保持する。
使われ方：密度余錐の変換同型を、元の fiber 上の写像の同型へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (A X : SSet.{u}) (x z : X _⦋0⦌)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : A ⟶ X))

/-- 元の全変換の prism を、区間と二つのパラメータの順に読む。 -/
def constantIntervalJointPrism : (Δ[1] : SSet.{u}) ⊗ (A ⊗ T) ⟶ X :=
  (α_ Δ[1] A T).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (𝟙 T)

lemma constantIntervalJointPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ T) ≫ constantIntervalJointPrism A X x z = SSet.const x := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (𝟙 T) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_zero, SSet.comp_const]

lemma constantIntervalJointPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ T) ≫ constantIntervalJointPrism A X x z = SSet.const z := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (𝟙 T) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_one, SSet.comp_const]

/-- 元の定値図式間の変換を、二頂点の区間写像への A パラメータ族へ移す。 -/
def constantIntervalTranspose : T ⟶ (ihom A).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (constantIntervalJointPrism A X x z)
    (constantIntervalJointPrism_zero A X x z) (constantIntervalJointPrism_one A X x z))

/-- curry の指定頂点は、同じパラメータを固定した元の射を表す。 -/
lemma curry_vertex_partial {B Y Z : SSet.{u}} (g : B ⊗ Y ⟶ Z) (y : Y _⦋0⦌) :
    (curry g).app (Opposite.op ⦋0⦌) y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (𝟙 B) (SSet.const y) ≫ g) := by
  have hh : lift (𝟙 B) (SSet.const y) ≫ g =
      uncurry' ((SSet.unitHomEquiv Y).symm y ≫ curry g) := by
    rw [uncurry', uncurry_natural_left, uncurry_curry]
    rfl
  rw [hh]
  change _ = SSet.unitHomEquiv _
    (curry' (uncurry' ((SSet.unitHomEquiv Y).symm y ≫ curry g)))
  rw [curry'_uncurry']
  exact (congrArg ((curry g).app (Opposite.op ⦋0⦌))
    ((SSet.unitHomEquiv Y).apply_symm_apply y)).symm

/-- 同じ区間 prism を持つ指定族は、元の変換頂点の転置そのもの。 -/
lemma constantIntervalTranspose_vertex (t : T _⦋0⦌) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f = (β_ Δ[1] A).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t).toTruncated).h) :
    (constantIntervalTranspose A X x z).app (Opposite.op ⦋0⦌) t = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
  rw [constantIntervalTranspose, curry_vertex_partial]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints, hf]
  have hh : (Δ[1] ◁ lift (𝟙 A) (SSet.const t)) ≫ constantIntervalJointPrism A X x z =
      (β_ Δ[1] A).hom ≫
        lift (𝟙 (A ⊗ (Δ[1] : SSet.{u})))
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (SSet.yonedaEquiv.symm t) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, a⟩
    rfl
  rw [hh, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_vertex]
  simp only [Category.assoc, lift_fst_assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

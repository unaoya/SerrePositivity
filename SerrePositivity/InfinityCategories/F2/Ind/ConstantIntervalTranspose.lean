module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFunctorHomPrism
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F2.ConstantTransformationVertex

/-!
概要：定値図式間の全変換空間を、元の二頂点間の区間写像のパラメータ族へ転置する。
方針：元の全 prism の因子を結合し直し、同じ両端条件で区間へ curry する。
規約：全てのパラメータと高次単体を保持する。
使われ方：密度余錐の変換同型を、元の fiber 上の写像の同型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (A X : SSet.{u}) (x z : X _⦋0⦌)
local notation "T" => intervalMappingSpace (functorVertex (SSet.const x : A ⟶ X))
  (functorVertex (SSet.const z : A ⟶ X))

/-- 元の全変換の prism を、区間と二つのパラメータの順に読む。 -/
def constantIntervalJointPrism : (Δ[1] : SSet.{u}) ⊗ (A ⊗ T) ⟶ X :=
  (α_ Δ[1] A T).inv ≫ intervalFunctorHomPrism (𝟙 T)

lemma constantIntervalJointPrism_zero :
    prismEndpoint 0 (A ⊗ T) ≫ constantIntervalJointPrism A X x z = SSet.const x := by
  change (prismEndpoint 0 A ▷ T) ≫ intervalFunctorHomPrism (𝟙 T) = _
  rw [intervalFunctorHomPrism_zero, SSet.comp_const]

lemma constantIntervalJointPrism_one :
    prismEndpoint 1 (A ⊗ T) ≫ constantIntervalJointPrism A X x z = SSet.const z := by
  change (prismEndpoint 1 A ▷ T) ≫ intervalFunctorHomPrism (𝟙 T) = _
  rw [intervalFunctorHomPrism_one, SSet.comp_const]

/-- 元の定値図式間の変換を、二頂点の区間写像への A パラメータ族へ移す。 -/
def constantIntervalTranspose : T ⟶ (ihom A).obj (intervalMappingSpace x z) :=
  curry (intervalMappingCurryOfEndpoints (constantIntervalJointPrism A X x z)
    (constantIntervalJointPrism_zero A X x z) (constantIntervalJointPrism_one A X x z))

/-- curry の指定頂点は、同じパラメータを固定した元の射を表す。 -/
lemma curry_vertex_partial {B Y Z : SSet.{u}} (g : B ⊗ Y ⟶ Z) (y : Y _⦋0⦌) :
    (curry g).app (Opposite.op ⦋0⦌) y =
      functorVertex (lift (𝟙 B) (SSet.const y) ≫ g) := by
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
lemma constantIntervalTranspose_vertex (t : T _⦋0⦌) (f : A ⟶ intervalMappingSpace x z)
    (hf : intervalMappingUncurry f = (β_ Δ[1] A).hom ≫
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated).h) :
    (constantIntervalTranspose A X x z).app (Opposite.op ⦋0⦌) t = functorVertex f := by
  rw [constantIntervalTranspose, curry_vertex_partial]
  apply congrArg functorVertex
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_curryOfEndpoints, hf]
  have hh : (Δ[1] ◁ lift (𝟙 A) (SSet.const t)) ≫ constantIntervalJointPrism A X x z =
      (β_ Δ[1] A).hom ≫
        lift (𝟙 (A ⊗ (Δ[1] : SSet.{u})))
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        F2.constantTransformationPrism (SSet.yonedaEquiv.symm t) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, a⟩
    rfl
  rw [hh, F2.constantTransformationPrism_vertex]
  simp only [Category.assoc, lift_fst_assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Ind

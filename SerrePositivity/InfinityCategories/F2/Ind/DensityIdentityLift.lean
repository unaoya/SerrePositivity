module

public import SerrePositivity.InfinityCategories.F2.Ind.MappingVertexLiftPrism
public import SerrePositivity.InfinityCategories.F2.Ind.DensityIdentityPointedStart
public import SerrePositivity.InfinityCategories.F2.Ind.CanonicalIntervalYonedaValue

/-!
概要：恒等点復元射上の同じ密度評価の持ち上げを、始値と終値を保って取り出す。
方針：c1 の指定変換頂点の全持ち上げを、元の恒等点復元射で制限する。
規約：始値は同じ canonical 恒等点、終値の元の値写像は同値。
使われ方：同じ底の区間族の普遍輸送との選択独立性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "A" => presheafDensityFiberParameter F x
local notation "E" => presheafDensityElementsParameter F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x
local notation "t" => presheafDensityEvaluatedTransformationVertex F x
local notation "r" => presheafDensityIdentityReconstruction F x

/-- 元の評価密度変換の c1 の持ち上げを、同じ恒等点上の全 fiber で制限する。 -/
def presheafDensityIdentityLiftPrism : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  mappingVertexLiftPrism Dx (SSet.const z) t r

/-- 同じ全持ち上げの始値は、元の Tw 全体からの恒等点に定値。 -/
lemma presheafDensityIdentityLiftPrism_start :
    prismEndpoint 0 A ≫ presheafDensityIdentityLiftPrism F x =
      SSet.const (canonicalYonedaPointedIdentity x).val := by
  rw [presheafDensityIdentityLiftPrism, mappingVertexLiftPrism_start,
    presheafDensityIdentityReconstruction_pointed]

/-- 同じ c1 の持ち上げの終値を、元の指定値の pointed fiber 内で読む。 -/
def presheafDensityIdentityLiftEndpoint :=
  r ≫ (leftUnstraighteningMappingVertexMap Dx (SSet.const z) t).val ≫
    F2.constantUnstraighteningFiberProjection E z

/-- 同じ全持ち上げの終値は、元の pointed fiber 内の終値そのもの。 -/
lemma presheafDensityIdentityLiftPrism_finish :
    prismEndpoint 1 A ≫ presheafDensityIdentityLiftPrism F x =
      presheafDensityIdentityLiftEndpoint F x ≫ vertexFiberι pointedSpaceProjection z := by
  rw [presheafDensityIdentityLiftPrism, mappingVertexLiftPrism_finish,
    presheafDensityIdentityLiftEndpoint]
  simp only [Category.assoc, F2.constantUnstraighteningFiberProjection,
    F2.constantPullbackFiberIso_fst_ι]

/-- この同じ終値の値写像は、元の評価密度変換の同じ fiber 上の値写像。 -/
lemma presheafDensityIdentityLiftEndpoint_value :
    presheafDensityIdentityLiftEndpoint F x ≫ (pointedSpaceFiberValueEquivalence z).hom =
      r ≫ presheafDensityEvaluatedFiberMap F x := by
  have hv := (presheafDensityEvaluatedFiberMap_vertex F x).trans
    (F2.coherentConstantTargetMap_vertex Dx z t)
  have he := functorVertex_injective hv
  simpa only [presheafDensityIdentityLiftEndpoint, Category.assoc] using
    congrArg (fun f => r ≫ f) he.symm

/-- 同じ持ち上げの終値の値写像自身が同値。 -/
lemma presheafDensityIdentityLiftEndpoint_value_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityIdentityLiftEndpoint F x ≫
      (pointedSpaceFiberValueEquivalence z).hom) := by
  rw [presheafDensityIdentityLiftEndpoint_value]
  exact (presheafDensityNativeIdentityValue_isQCatEquivalence F x).ofFunctorIso
    (FunctorIso.precomp (presheafDensityEvaluationFiberIso F x) r)

end SerrePositivity.InfinityCategories.F2.Ind

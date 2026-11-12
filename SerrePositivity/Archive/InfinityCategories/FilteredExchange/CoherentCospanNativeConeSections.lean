module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedConeSections
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanPointedConeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativePointFunctorIso

/-!
概要：元の小さい fiber の全点を native な cospan 錐の切断族として表示する。
方針：始点族を既存の二つの fiber 同型へ同定し、全錐の始点制限で同値性を反映する。
規約：元の全 pointed 持ち上げを使用。使われ方：模型 fiber 比較の同値性への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "j" => joinInl Δ[0] (horn 2 2)
local notation "v" => NatTrans.app (j ≫ Subtype.val c)
  (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection F) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 全錐の始点の実際の零単体は元の値の頂点である。 -/
lemma coherentCospanNativeConeInitialVertex : F.app (Opposite.op ⦋0⦌) (ULift.up b) = v := by
  rw [HomotopyLimits.coherentCone_inl_vertex, SSet.yonedaEquiv_symm_zero]
  change F.app _ (ULift.up b) =
    SpaceInfinity.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op (c).vertex
  have hz : ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op = 𝟙 _ := Subsingleton.elim _ _
  rw [hz, (SpaceInfinity.{u}).map_id]
  exact (coherentCospanConePointwiseCone_vertex F X Y Z C b).symm

/-- 始点族は、小さい fiber から元の pointed fiber への厳密な同型の順方向。 -/
def coherentCospanFiberPointedSourceIso : a ≅ vertexFiber pointedSpaceProjection v :=
  smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b) ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection)
      (coherentCospanNativeConeInitialVertex F X Y Z C b))

lemma coherentCospanFiberPointedSourceIso_hom_ι :
    (coherentCospanFiberPointedSourceIso F X Y Z C b).hom ≫
      vertexFiberι pointedSpaceProjection v = s := by
  dsimp only [coherentCospanFiberPointedSourceIso, Iso.trans_hom, eqToIso.hom]
  simp only [Category.assoc]
  rw [vertexFiberTransport_ι pointedSpaceProjection
    (coherentCospanNativeConeInitialVertex F X Y Z C b),
    leftUnstraighteningFiberIso_hom_ι, ← Category.assoc,
    smallLeftUnstraighteningFiberIso_hom_ι]
  rfl

/-- 始点の実際の相対 curry は、同型である一点評価との合成が元の fiber 同型になる。 -/
lemma coherentCospanNativeInitialSections_evaluate :
    nativePointedConeInitialSections c s hs ≫
      (relativePointFunctorIso pointedSpaceProjection (j ≫ (c).val)).hom =
      (coherentCospanFiberPointedSourceIso F X Y Z C b).hom := by
  apply vertexFiber_hom_ext pointedSpaceProjection v
  rw [Category.assoc, coherentCospanFiberPointedSourceIso_hom_ι]
  exact nativePointedConeInitialSections_evaluate_ι c s hs

/-- 始点の相対 curry の同値性は、既存の二つの fiber 同型から従う。 -/
lemma coherentCospanNativeInitialSections_isQCatEquivalence :
    IsQCatEquivalence (nativePointedConeInitialSections c s hs) := by
  apply (qCatEquivalenceOfIso
    (relativePointFunctorIso pointedSpaceProjection (j ≫ (c).val))).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (nativePointedConeInitialSections c s hs ≫
    (relativePointFunctorIso pointedSpaceProjection (j ≫ (c).val)).hom)
  rw [coherentCospanNativeInitialSections_evaluate]
  exact (qCatEquivalenceOfIso (coherentCospanFiberPointedSourceIso F X Y Z C b)).isQCatEquivalence

/-- 元の全 pointed 錐を制限して得る、元の図式上の切断の実際の族。 -/
def coherentCospanNativeConeSections := nativePointedConeSections c s hs

/-- 切断族の展開は、元の全 pointed 錐の図式部分への同じ厳密な制限。 -/
lemma coherentCospanNativeConeSections_uncurry :
    relativeFunctorUncurry (coherentCospanNativeConeSections F X Y Z C b) =
      (joinInr Δ[0] (horn 2 2) ▷ a) ≫ coherentCospanPointedConeLift F X Y Z C b :=
  nativePointedConeSections_uncurry c s hs

/-- 各点の native 錐が極限なら、元の fiber の切断族は同値。 -/
lemma coherentCospanNativeConeSections_isQCatEquivalence (hc : IsLimitCone c) :
    IsQCatEquivalence (coherentCospanNativeConeSections F X Y Z C b) :=
  nativePointedConeSections_isQCatEquivalence c s hs hc
    (coherentCospanNativeInitialSections_isQCatEquivalence F X Y Z C b)

end SerrePositivity.InfinityCategories.F2

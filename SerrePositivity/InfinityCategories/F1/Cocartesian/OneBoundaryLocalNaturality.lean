module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryLocalTarget
public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneHornLocalNaturality
public import SerrePositivity.InfinityCategories.F1.PairedKanFunctorIso

/-!
概要：標準一単体の全局所 Hom 比較を、元の一次元境界比較へ指定同型で制限する。
方針：両端の同じ指定自然性を対にし、実際の target 積分解の逆で境界へ戻す。
規約：元の全局所 Hom と同じ境界比較を保持する。
使われ方：高次の欠けた面の境界で比較を揃える初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "N" => (cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "T" => Functor.op (uliftOverFunctor (nerve C)) ⋙ intervalDiagramOverFunctor P Q

local instance (z : Over ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :
    KanComplex ((intervalDiagramOverFunctor P Q).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (intervalMappingSpace
    (functorVertex (z.hom ≫ P)) (functorVertex (z.hom ≫ Q))))

/-- 元の全局所 Hom の同じセル比較と、同じ境界比較との指定自然性。 -/
def cocartesianOneBoundaryHomComparison_localNaturalityIso :
    FunctorIso
      ((N).map (boundarySimplexOverMap 0 σ).op ≫ cocartesianOneBoundaryHomComparison i σ p q)
      (cocartesianStandardSimplexHomComparison σ p q ≫
        (T).map (boundarySimplexOverMap 0 σ).op) := by
  have h : FunctorIso
      (((N).map (boundarySimplexOverMap 0 σ).op ≫
        cocartesianOneBoundaryHomComparison i σ p q) ≫
          (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom)
      ((cocartesianStandardSimplexHomComparison σ p q ≫
        (T).map (boundarySimplexOverMap 0 σ).op) ≫
          (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom) := by
    apply F2.functorIsoOfEq (pairedKanFunctorIso
      (cocartesianStandardSimplexHomComparison_naturalityIso (stdSimplex.δ i) σ p q)
      (cocartesianOneHornHomComparison_localNaturalityIso i σ p q))
    · simpa only [cocartesianOneBoundaryLocalSourceFace,
        cocartesianOneBoundaryLocalSourceHorn, faceSimplexOverMap, hornSimplexOverMap,
        hornOneSimplexOverMap, HornBoundaryOver.face, Over.mk_hom, intervalDiagramOverFunctor]
        using (cocartesianOneBoundaryHomComparison_localSourceProduct i σ p q).symm
    · simpa only [cocartesianOneBoundaryLocalTargetFace,
        cocartesianOneBoundaryLocalTargetHorn, faceSimplexOverMap, hornSimplexOverMap,
        hornOneSimplexOverMap, HornBoundaryOver.face, Functor.comp_obj, Functor.comp_map,
        Functor.op_obj, Functor.op_map, uliftOverFunctor, Over.mk_hom, intervalDiagramOverFunctor,
        Quiver.Hom.unop_op, Opposite.unop_op]
        using (cocartesianOneBoundaryHomComparison_localTargetProduct i σ p q).symm
  apply F2.functorIsoOfEq (h.postcomp (cocartesianOneBoundaryIntervalProductIso i σ P Q).inv)
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories

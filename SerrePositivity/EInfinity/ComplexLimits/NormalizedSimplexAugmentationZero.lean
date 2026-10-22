module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedHomZeroRawEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexCochainContraction
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationValues

/-!
# 元の正規化単体 augmentation の零次数生成元での値

概要：元の零次数単体の同じ生成元は同じ augmentation により 1 へ送られる。
方針：Moore 零次数包含と同じ逆を相殺し、元の自由加群 augmentation を評価する。
規約：元の単体・収縮の順方向・自由生成元を保つ。
使われ方：普遍 Hom 族の augmentation 像の恒等辺への同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedSimplexChainAugmentation_zero (n : SimplexCategory)
    (x : (SSet.stdSimplex.obj n : SSet.{0}) _⦋0⦌) :
    (normalizedSimplexChainContraction A n).hom.f 0
      ((mooreDegreeZeroIso ((BarrattEccles.linearization A).obj
        (SSet.stdSimplex.obj n))).inv (ModuleCat.freeMk (ULift.up x))) = (1 : A) := by
  simp only [normalizedSimplexChainContraction, HomotopyEquiv.trans_hom,
    HomologicalComplex.comp_f, ModuleCat.comp_apply, ChainComplex.single₀_obj_zero,
    SimplicialObject.Augmented.point_obj, AlgebraicTopology.alternatingFaceMapComplex_obj_X,
    AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex_hom,
    AlgebraicTopology.inclusionOfMooreComplexMap_f,
    AlgebraicTopology.NormalizedMooreComplex.objX_zero]
  change (ModuleCat.FreeMonoidal.εIso A).inv
    ((ModuleCat.free A).map _ ((ModuleCat.free A).map _ ((ModuleCat.free A).map _
      ((mooreDegreeZeroIso ((BarrattEccles.linearization A).obj
        (SSet.stdSimplex.obj n))).hom
        ((mooreDegreeZeroIso ((BarrattEccles.linearization A).obj
          (SSet.stdSimplex.obj n))).inv (ModuleCat.freeMk (ULift.up x))))))) = (1 : A)
  rw [Iso.inv_hom_id_apply]
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply, ModuleCat.free_map_apply,
    ModuleCat.FreeMonoidal.εIso_inv_freeMk]

end SerrePositivity.EInfinity.ComplexLimits

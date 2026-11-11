module

public import SerrePositivity.KST.Spectra.ZeroSkeletonPoint
public import SerrePositivity.KST.Spectra.SkeletalInitialDetection
public import SerrePositivity.KST.Spectra.ConstantMappingRetraction

/-!
概要：正次数 cohomology の消滅から頂点評価の単射性と定数写像の全射性を得る。
方針：零骨格を一点へ同定して制限の検出を評価へ移し、評価による分裂を使う。
規約：群の次数は二以上。源に選んだ頂点と一頂点性を要求する。
使われ方：Goerss–Jardine VIII §2。有理自明作用の各段での Shapiro の全射性。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory SSet Opposite
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 前合成後の頂点評価は合成した頂点での評価。 -/
lemma pre_evaluation {K L : SSet.{u}} (f : K ⟶ L) (v : (𝟙_ SSet.{u}) ⟶ K)
    (Y : PointedSimplicialSet.{u}) : pre f Y ≫ evaluation v Y = evaluation (v ≫ f) Y := by
  have he := (contravariantFunctor Y).map_comp f.op v.op
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ (unitIso Y).hom) he.symm)

variable (K : SSet.{u}) [Subsingleton (K _⦋0⦌)] (v : K _⦋0⦌)
  (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
  (hfirst : IsZero ((NormalizedValueCochains.complex K
    (AddCommGrpCat.of (SkeletalCellAttachment.positiveAdditiveCoefficient Y 0 r))).homology 1))
  (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
    (AddCommGrpCat.of
      (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))

include hfirst hH in
/-- 通常の写像空間の高次群の頂点評価は単射。 -/
theorem evaluationGroupMap_injective_of_isZero :
    Function.Injective (pointedGroupMap (r + 1) (evaluation (SSet.const v) Y)) := by
  let e := evaluation (initialVertexMap K v) Y
  have : IsIso (pre (initialVertexMap K v) Y) :=
    inferInstanceAs (IsIso ((contravariantFunctor Y).map (initialVertexMap K v).op))
  have : IsIso e := by dsimp only [e, evaluation]; infer_instance
  let ei : (obj (K.skeleton 1 : SSet.{u}) Y).right ≅ Y.right :=
    PointedSimplicialSet.forget.mapIso (asIso e)
  have hinj : Function.Injective (pointedGroupMap (r + 1) e) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) ei
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e)).injective
  let f : obj K Y ⟶ obj (K.skeleton 1 : SSet.{u}) Y := pre (K.skeleton 1).ι Y
  have he : f ≫ e = evaluation (SSet.const v) Y := by
    change pre (K.skeleton 1).ι Y ≫ evaluation (initialVertexMap K v) Y = _
    rw [pre_evaluation, initialVertexMap_ι]
  intro a b hab
  apply stageZeroGroupMap_injective_of_isZero K Y r hfirst hH
  change pointedGroupMap (r + 1) f a = pointedGroupMap (r + 1) f b
  apply hinj
  rw [← pointedGroupMap_comp, ← pointedGroupMap_comp, he]
  exact hab

include v hfirst hH in
/-- 正次数 cohomology が消滅する一頂点の源では、高次の類は定数写像から来る。 -/
theorem constant_groupMap_surjective_of_isZero :
    Function.Surjective (pointedGroupMap (r + 1) (constant K Y)) := by
  intro a
  refine ⟨pointedGroupMap (r + 1) (evaluation (SSet.const v) Y) a, ?_⟩
  apply evaluationGroupMap_injective_of_isZero K v Y r hfirst hH
  rw [← pointedGroupMap_comp, constant_evaluation, pointedGroupMap_id]

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping

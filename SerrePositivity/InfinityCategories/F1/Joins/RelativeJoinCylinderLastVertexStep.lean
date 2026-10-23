module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderFrontPushout
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinStdSimplexPushout
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinPrismAnodyne
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderNaturality
public import SerrePositivity.InfinityCategories.Core.PrecompositionPushoutGluing

/-!
概要：最後の頂点を保つ標準単体間の射の写像円柱比較の境界からの帰納段階。
方針：二つの pushout の間の比較を、Z(0) から Z(m) への同値条件と境界の比較から貼る。
規約：境界の比較の同値条件だけを帰納仮定とする。
使われ方：Kerodon Proposition 5.2.4.5、f(m)=n の場合の次元帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：境界の写像円柱の比較と全体の比較は境界の包含について可換。
方針：境界円柱の二つの包含で prism と右包含の自然性を使う。
規約：終域 Y は任意。
使われ方：Kerodon Proposition 5.2.4.5、比較の立方体の側面の可換性。 -/
lemma relativeJoinBoundaryCylinderComparison_naturality {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinCylinderComparison ((boundary m).ι ≫ f) ≫
        relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      relativeJoinBoundaryCylinderMap f ≫ relativeJoinCylinderComparison f := by
  let u : Over.mk ((boundary m).ι ≫ f) ⟶ Over.mk f := Over.homMk (boundary m).ι rfl
  have hp : relativeJoinPrism ((boundary m).ι ≫ f) ≫ relativeJoinLeftMap (𝟙 Y)
      (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ≫ relativeJoinPrism f :=
    relativeJoinPrism_naturality u
  have hr : relativeJoinInr ((boundary m).ι ≫ f) (𝟙 Y) ≫ relativeJoinLeftMap (𝟙 Y)
      (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl = relativeJoinInr f (𝟙 Y) :=
    relativeJoinInr_leftMap u
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderComparison_inl, hp,
      ← Category.assoc, relativeJoinBoundaryCylinderMap_inl, Category.assoc,
      relativeJoinCylinderComparison_inl]
  · rw [← Category.assoc, relativeJoinCylinderComparison_inr, hr,
      ← Category.assoc, relativeJoinBoundaryCylinderMap_inr, relativeJoinCylinderComparison_inr]

/-- 概要：初期部分から境界の写像円柱を経由する比較は Z(m) の境界への因子化と一致する。
方針：境界 relative join の包含後に、円柱比較の自然性と既知の二つの可換性を使う。
規約：終域 Y は任意。
使われ方：Kerodon Proposition 5.2.4.5、比較の立方体の上面の可換性。 -/
lemma relativeJoinCylinder_boundary_cube {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialCylinderMap f ≫ relativeJoinCylinderComparison ((boundary m).ι ≫ f) =
      Subcomplex.homOfLE (relativeJoinPrismInitial_le_penultimate m) ≫
        relativeJoinPrismPenultimateBoundaryLift f := by
  apply (cancel_mono (relativeJoinLeftMap (𝟙 Y)
    (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)).1
  rw [Category.assoc, relativeJoinBoundaryCylinderComparison_naturality f,
    ← Category.assoc, relativeJoinPrismInitialCylinderMap_square,
    Category.assoc, relativeJoinCylinderComparison_inl,
    Category.assoc, relativeJoinPrismPenultimateBoundaryLift_comp,
    ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：最後の頂点を保つ標準単体間の射の比較の同値条件は境界の比較から従う。
方針：写像円柱と relative join の二つの pushout に三頂点の同値条件の貼り合わせを使う。
規約：境界の比較を帰納仮定とし、一般の構造射の比較の同値性を仮定しない。
使われ方：Kerodon Proposition 5.2.4.5、標準単体の最後の頂点を保つ場合の帰納段階。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_lastVertex_of_boundary
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (hboundary : IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((boundary m).ι ≫ f))) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f) := by
  apply isPrecompositionEquivalence_of_pushout_gluing
    (relativeJoinCylinder_front_isPushout f).flip
    (relativeJoin_stdSimplex_prism_isPushout f hf).flip
    (Subcomplex.homOfLE (relativeJoinPrismInitial_le_penultimate m)) (𝟙 _)
    (relativeJoinCylinderComparison ((boundary m).ι ≫ f)) (relativeJoinCylinderComparison f)
  · rw [Category.comp_id, Subcomplex.homOfLE_ι]
  · exact relativeJoinCylinder_boundary_cube f
  · rw [relativeJoinCylinderComparison_inl, Category.id_comp]
  · exact (relativeJoinBoundaryCylinderComparison_naturality f).symm
  · exact isPrecompositionEquivalence_relativeJoinPrismInitial_penultimate m
  · exact isPrecompositionEquivalence_id _
  · exact hboundary

end SerrePositivity.InfinityCategories

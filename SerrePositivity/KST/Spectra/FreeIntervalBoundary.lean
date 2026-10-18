module

public import SerrePositivity.KST.Spectra.FreePathSpace
public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：自由な区間の境界とその点つき写像空間。
方針：二つの頂点の余積に基点を加え、反変内部 Hom の極限保存を使う。
規約：境界の第一成分が終点、第二成分が始点。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。両端点の同時評価。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : PointedSimplicialSet.adjoinBasepointFunctor.{u}.IsLeftAdjoint :=
  PointedSimplicialSet.adjoinBasepointAdjunction.isLeftAdjoint

/-- 概要：自由な基点を加えた区間の二つの端点。
方針：終単体集合の二項余積に自由な基点を加える。
規約：smash の単位二つの点つき余積となる。
使われ方：Goerss–Jardine I §7。両端点の同時指定の源。 -/
def freeIntervalBoundary : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepoint ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))

/-- 概要：自由な境界の終点成分。
方針：第一の余積包含に基点を加える。
規約：面添字零の端点に対応する。
使われ方：Goerss–Jardine I §7。境界上の終点評価。 -/
def freeBoundaryEnd : 𝟙_ PointedSimplicialSet.{u} ⟶ freeIntervalBoundary.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (coprod.inl : 𝟙_ SSet.{u} ⟶ _)

/-- 概要：自由な境界の始点成分。
方針：第二の余積包含に基点を加える。
規約：面添字一の端点に対応する。
使われ方：Goerss–Jardine I §7。境界上の始点評価。 -/
def freeBoundaryStart : 𝟙_ PointedSimplicialSet.{u} ⟶ freeIntervalBoundary.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (coprod.inr : 𝟙_ SSet.{u} ⟶ _)

/-- 概要：自由な境界から自由な区間への包含。
方針：二つの端点の基礎射に自由な基点を加える。
規約：両端点を同時に含める射。
使われ方：Goerss–Jardine I §7、HTT A.3.3。両端点評価の fibration 性。 -/
def freeBoundaryInclusion : freeIntervalBoundary.{u} ⟶ freeInterval.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map intervalEndpoint.{u}.right

/-- 概要：自由な境界の包含は基礎単体集合で単射。
方針：二端点の単射性と基点追加による単射の保存を使う。
規約：HT-KQ を使わない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。境界への内部 Hom の制限。 -/
instance freeBoundaryInclusion_mono : Mono freeBoundaryInclusion.{u}.right :=
  mono_coprod_map_id intervalEndpoint.{u}.right

/-- 概要：境界の終点から区間へ進むと自由な終点包含。
方針：零次面の定数射表示を基点追加へ移す。
規約：面添字零。
使われ方：Goerss–Jardine I §7。終点の評価の同定。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEnd_inclusion : freeBoundaryEnd.{u} ≫ freeBoundaryInclusion =
    freeIntervalEndpoint 0 := by
  have h : PointedSimplicialSet.deltaZeroUnitIso.inv ≫ stdSimplex.δ.{u} (0 : Fin 2) =
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 1) := by
    rw [stdSimplex.δ_zero_eq_const, SSet.comp_const]
  change PointedSimplicialSet.adjoinBasepointFunctor.{u}.map coprod.inl ≫
    PointedSimplicialSet.adjoinBasepointFunctor.{u}.map intervalEndpoint.{u}.right = _
  rw [← Functor.map_comp, intervalEndpoint_inl]
  change _ = PointedSimplicialSet.adjoinBasepointFunctor.{u}.map
    PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫
      PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (stdSimplex.δ.{u} (0 : Fin 2))
  rw [← Functor.map_comp, h]

/-- 概要：境界の始点から区間へ進むと自由な始点包含。
方針：一次面の定数射表示を基点追加へ移す。
規約：面添字一。
使われ方：Goerss–Jardine I §7。始点の評価の同定。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryStart_inclusion : freeBoundaryStart.{u} ≫ freeBoundaryInclusion =
    freeIntervalEndpoint 1 := by
  have h : PointedSimplicialSet.deltaZeroUnitIso.inv ≫ stdSimplex.δ.{u} (1 : Fin 2) =
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 0) := by
    rw [stdSimplex.δ_one_eq_const, SSet.comp_const]
  change PointedSimplicialSet.adjoinBasepointFunctor.{u}.map coprod.inr ≫
    PointedSimplicialSet.adjoinBasepointFunctor.{u}.map intervalEndpoint.{u}.right = _
  rw [← Functor.map_comp, intervalEndpoint_inr]
  change _ = PointedSimplicialSet.adjoinBasepointFunctor.{u}.map
    PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫
      PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (stdSimplex.δ.{u} (1 : Fin 2))
  rw [← Functor.map_comp, h]

/-- 概要：自由な境界は二つの点つき単位の余積。
方針：基点追加が左随伴として二項余積を保存することを使う。
規約：基礎単体集合の余積ではなく点つき圏の余積。
使われ方：HTT A.3.3、Goerss–Jardine I §7。境界からの Hom の積表示。 -/
def freeBoundaryIsColimit :
    IsColimit (BinaryCofan.mk freeBoundaryEnd.{u} freeBoundaryStart) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit
    PointedSimplicialSet.adjoinBasepointFunctor (𝟙_ SSet.{u}) (𝟙_ SSet.{u})

/-- 概要：自由な境界からの写像空間は二つの単位からの写像空間の積。
方針：反変写像空間関手が極限を保つことを余積の反対に適用する。
規約：基礎単体集合の積の普遍性を述べる。
使われ方：HTT A.3.3、Goerss–Jardine I §7。両端点評価の相対充填。 -/
def freeBoundaryHomIsLimit (Y : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (PointedMapping.pre freeBoundaryEnd.{u} Y)
      (PointedMapping.pre freeBoundaryStart.{u} Y)) := by
  have h := mapIsLimitOfPreservesOfIsLimit (cofiberMappingFunctor Y) _ _
    (BinaryCofan.IsColimit.op freeBoundaryIsColimit.{u})
  change IsLimit (BinaryFan.mk ((cofiberMappingFunctor Y).map freeBoundaryEnd.{u}.op)
    ((cofiberMappingFunctor Y).map freeBoundaryStart.{u}.op)) at h
  rw [cofiberMappingFunctor_map, cofiberMappingFunctor_map] at h
  exact h

/-- 概要：点つき内部 Hom の源の制限は合成を逆順に保つ。
方針：閉構造の pre との一致とその反変関手性を使う。
規約：点つき射の厳密な等式。
使われ方：HTT A.3.3、BF 1978 §2。境界の成分評価。 -/
theorem PointedMapping.prePointed_comp {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : B ⟶ C) (Y : PointedSimplicialSet.{u}) :
    PointedMapping.prePointed j Y ≫ PointedMapping.prePointed i Y =
      PointedMapping.prePointed (i ≫ j) Y := by
  simp only [PointedMapping.prePointed_eq_closedPre]
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]

/-- 概要：自由な境界上の終点を評価する点つき射。
方針：終点成分へ制限して単位の内部 Hom を評価する。
規約：面添字零の端点。
使われ方：Goerss–Jardine I §7。両端点写像空間の積の第一射影。 -/
def freeBoundaryHomEnd (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom freeIntervalBoundary.{u} Y ⟶ Y :=
  PointedMapping.prePointed freeBoundaryEnd.{u} Y ≫ (unitIsoSelf (X := Y)).hom

/-- 概要：自由な境界上の始点を評価する点つき射。
方針：始点成分へ制限して単位の内部 Hom を評価する。
規約：面添字一の端点。
使われ方：Goerss–Jardine I §7。両端点写像空間の積の第二射影。 -/
def freeBoundaryHomStart (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom freeIntervalBoundary.{u} Y ⟶ Y :=
  PointedMapping.prePointed freeBoundaryStart.{u} Y ≫ (unitIsoSelf (X := Y)).hom

/-- 概要：自由な境界からの写像空間は標的二つの積。
方針：単位からの内部 Hom の同型を二つの射影へ合成する。
規約：基礎単体集合の積。
使われ方：HTT A.3.3、Goerss–Jardine I §7。両端点の同時評価。 -/
def freeBoundaryEvaluationIsLimit (Y : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (freeBoundaryHomEnd Y).right (freeBoundaryHomStart Y).right) := by
  let e := PointedSimplicialSet.forget.mapIso (unitIsoSelf (X := Y))
  exact BinaryFan.isLimitCompRightIso _ e.hom
    (BinaryFan.isLimitCompLeftIso _ e.hom (freeBoundaryHomIsLimit Y))

/-- 概要：自由な境界からの写像空間と標的の二項積との標準同型。
方針：二つの積の普遍性を比較する。
規約：第一成分が終点、第二成分が始点。
使われ方：HTT A.3.3、BF 1978 §2。境界制限の fibration を積へ移す。 -/
def freeBoundaryEvaluationIso (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom freeIntervalBoundary.{u} Y).right ≅ Y.right ⨯ Y.right :=
  (freeBoundaryEvaluationIsLimit Y).conePointUniqueUpToIso
    (t := BinaryFan.mk (prod.fst : Y.right ⨯ Y.right ⟶ Y.right) prod.snd)
    (prodIsProd Y.right Y.right)

/-- 概要：境界評価の標準同型の第一射影は終点評価。
方針：極限の標準比較同型の成分計算を使う。
規約：第一成分が終点。
使われ方：Goerss–Jardine I §7。mapping path の終点射影。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEvaluationIso_fst (Y : PointedSimplicialSet.{u}) :
    (freeBoundaryEvaluationIso Y).hom ≫ prod.fst = (freeBoundaryHomEnd Y).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp (freeBoundaryEvaluationIsLimit Y)
    (prodIsProd Y.right Y.right) ⟨WalkingPair.left⟩

/-- 概要：境界評価の標準同型の第二射影は始点評価。
方針：極限の標準比較同型の成分計算を使う。
規約：第二成分が始点。
使われ方：Goerss–Jardine I §7。mapping path の始点射影。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEvaluationIso_snd (Y : PointedSimplicialSet.{u}) :
    (freeBoundaryEvaluationIso Y).hom ≫ prod.snd = (freeBoundaryHomStart Y).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp (freeBoundaryEvaluationIsLimit Y)
    (prodIsProd Y.right Y.right) ⟨WalkingPair.right⟩

/-- 概要：自由な path の両端点を同時に評価する射。
方針：境界への制限と境界写像空間の積表示を合成する。
規約：第一射影が終点、第二射影が始点。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path の fibration 性。 -/
def freePathEndpoints (Y : PointedSimplicialSet.{u}) :
    (freePathSpace Y).right ⟶ Y.right ⨯ Y.right :=
  PointedMapping.pre freeBoundaryInclusion.{u} Y ≫ (freeBoundaryEvaluationIso Y).hom

/-- 概要：自由な path の両端点の同時評価は Kan fibration。
方針：単射な境界への制限の fibration と積表示の同型を合成する。
規約：HT-KQ は不要。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の fibration 置換。 -/
instance freePathEndpoints_fibration (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Fibration (freePathEndpoints Y) := by
  let : Fibration (PointedMapping.pre freeBoundaryInclusion.{u} Y) :=
    PointedMapping.pre_fibration freeBoundaryInclusion.{u} Y
  unfold freePathEndpoints
  infer_instance

/-- 概要：両端点の同時評価の第一射影は自由な path の終点評価。
方針：源の制限の合成と境界の終点包含を計算する。
規約：面添字零。
使われ方：BF 1978 §2。mapping path の終点写像。 -/
@[reassoc (attr := simp)]
theorem freePathEndpoints_fst (Y : PointedSimplicialSet.{u}) :
    freePathEndpoints Y ≫ prod.fst = (freePathEndpoint Y 0).right := by
  rw [freePathEndpoints, Category.assoc, freeBoundaryEvaluationIso_fst]
  have h : PointedMapping.prePointed freeBoundaryInclusion.{u} Y ≫ freeBoundaryHomEnd Y =
      freePathEndpoint Y 0 := by
    unfold freeBoundaryHomEnd freePathEndpoint
    rw [← Category.assoc, PointedMapping.prePointed_comp, freeBoundaryEnd_inclusion]
  exact congrArg Under.Hom.right h

/-- 概要：両端点の同時評価の第二射影は自由な path の始点評価。
方針：源の制限の合成と境界の始点包含を計算する。
規約：面添字一。
使われ方：BF 1978 §2。mapping path の始点写像。 -/
@[reassoc (attr := simp)]
theorem freePathEndpoints_snd (Y : PointedSimplicialSet.{u}) :
    freePathEndpoints Y ≫ prod.snd = (freePathEndpoint Y 1).right := by
  rw [freePathEndpoints, Category.assoc, freeBoundaryEvaluationIso_snd]
  have h : PointedMapping.prePointed freeBoundaryInclusion.{u} Y ≫ freeBoundaryHomStart Y =
      freePathEndpoint Y 1 := by
    unfold freeBoundaryHomStart freePathEndpoint
    rw [← Category.assoc, PointedMapping.prePointed_comp, freeBoundaryStart_inclusion]
  exact congrArg Under.Hom.right h

end

end SerrePositivity.KST.Spectra

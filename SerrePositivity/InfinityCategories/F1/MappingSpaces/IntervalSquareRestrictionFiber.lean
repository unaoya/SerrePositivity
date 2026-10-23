module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalBoundarySquareData

/-!
概要：実際の区間の境界制限 fiber と両端条件の fiber の同定。
方針：境界の全空間の同型で pointed space 側の条件を翻訳する。
規約：任意の高次パラメーターで二つの条件の同値を示す。
使われ方：Kerodon Lemma 5.6.9.1 の周囲の境界 fiber の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同型による前合成は指定された定値な関手の条件を保ち反映する。
方針：逆同型で前合成して元の等式を回収する。
規約：任意のパラメーター空間と任意の標的で成立する。
使われ方：境界の全空間と両端図式の条件の翻訳。 -/
lemma precomposition_const_iff_of_iso {A D X L : SSet.{u}} (e : A ⟶ D) [IsIso e]
    (H : L ⟶ (ihom D).obj X) (v : D ⟶ X) :
    H = SSet.const (functorVertex v) ↔
      H ≫ (pre e).app X = SSet.const (functorVertex (e ≫ v)) := by
  constructor
  · intro h
    rw [h, SSet.const_comp]
    rfl
  · intro h
    have h' := congrArg (fun w ↦ w ≫ (pre (inv e)).app X) h
    simp only [Category.assoc] at h'
    rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id,
      NatTrans.id_app, Category.comp_id, SSet.const_comp] at h'
    change H = SSet.const (functorVertex (inv e ≫ (e ≫ v))) at h'
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using h'

/-- 概要：境界上の四角形を指定することは底側と全空間側の両端条件と同値。
方針：引き戻しの二射影と境界の全空間の同型を使う。
規約：F は任意の高次パラメーターの族。
使われ方：実際の境界制限 fiber と同時端点 fiber の同型。 -/
lemma intervalSquareRestrictionCondition_iff {E L : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1}))
    (S : LeftTransportSquare (pullback.snd p (boundary 1).ι))
    (F : L ⟶ transportSquareSpace p) :
    F ≫ transportSquareRestriction p (boundary 1).ι = SSet.const (transportSquareVertex S) ↔
      F ≫ intervalSquareBoundaryConstraint p = SSet.const
        (functorVertex (intervalMappingBoundary
          (S.diagram.app _ (intervalBoundaryVertex 0))
          (S.diagram.app _ (intervalBoundaryVertex 1))),
          functorVertex (intervalBoundaryPointedMap
            (S.intervalBoundaryFiberMap 0) (S.intervalBoundaryFiberMap 1))) := by
  have hcomponents :
      F ≫ transportSquareRestriction p (boundary 1).ι = SSet.const (transportSquareVertex S) ↔
      F ≫ transportSquareDiagram p ≫ (pre (boundary 1).ι).app SpaceInfinity =
        SSet.const (functorVertex S.diagram) ∧
      F ≫ transportSquarePointed p ≫
          (pre (pullback.fst p (boundary 1).ι)).app PointedSpaceInfinity =
        SSet.const (functorVertex S.pointedMap) := by
    constructor
    · intro h
      constructor
      · have h' := congrArg (fun w ↦ w ≫ transportSquareDiagram (pullback.snd p (boundary 1).ι)) h
        rw [Category.assoc, transportSquareRestriction_diagram, SSet.const_comp,
          transportSquareVertex_diagram] at h'
        exact h'
      · have h' := congrArg (fun w ↦ w ≫ transportSquarePointed (pullback.snd p (boundary 1).ι)) h
        rw [Category.assoc, transportSquareRestriction_pointed, SSet.const_comp,
          transportSquareVertex_pointed] at h'
        exact h'
    · rintro ⟨hD, hP⟩
      apply pullback.hom_ext
      · change (F ≫ transportSquareRestriction p (boundary 1).ι) ≫
          transportSquarePointed _ = _
        rw [Category.assoc, transportSquareRestriction_pointed, SSet.const_comp]
        change _ = SSet.const ((transportSquarePointed (pullback.snd p (boundary 1).ι)).app _
          (transportSquareVertex S))
        rw [transportSquareVertex_pointed]
        exact hP
      · change (F ≫ transportSquareRestriction p (boundary 1).ι) ≫
          transportSquareDiagram _ = _
        rw [Category.assoc, transportSquareRestriction_diagram, SSet.const_comp]
        change _ = SSet.const ((transportSquareDiagram (pullback.snd p (boundary 1).ι)).app _
          (transportSquareVertex S))
        rw [transportSquareVertex_diagram]
        exact hD
  have hpointed := precomposition_const_iff_of_iso (intervalBoundaryTotalMap p)
    (F ≫ transportSquarePointed p ≫ (pre (pullback.fst p (boundary 1).ι)).app _)
    S.pointedMap
  simp only [Category.assoc] at hpointed
  rw [← NatTrans.comp_app, ← pre_map, intervalBoundaryTotalMap_fst,
    ← S.intervalBoundaryPointedMap_eq] at hpointed
  have heta : (SSet.const (functorVertex S.diagram) : L ⟶ _) =
      SSet.const (functorVertex (intervalMappingBoundary
        (S.diagram.app _ (intervalBoundaryVertex 0))
        (S.diagram.app _ (intervalBoundaryVertex 1)))) :=
    congrArg (fun w ↦ SSet.const (functorVertex w)) (intervalMappingBoundary_eta S.diagram).symm
  rw [hcomponents, hpointed, heta]
  constructor
  · rintro ⟨hD, hP⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [intervalSquareBoundaryConstraint, Category.assoc, lift_fst, SSet.const_comp]
      exact hD
    · simp only [intervalSquareBoundaryConstraint, Category.assoc, lift_snd, SSet.const_comp]
      exact hP
  · intro h
    constructor
    · have h' := congrArg (fun w ↦ w ≫ fst _ _) h
      simp only [intervalSquareBoundaryConstraint, Category.assoc, lift_fst, SSet.const_comp] at h'
      exact h'
    · have h' := congrArg (fun w ↦ w ≫ snd _ _) h
      simp only [intervalSquareBoundaryConstraint, Category.assoc, lift_snd, SSet.const_comp] at h'
      exact h'

/-- 概要：境界上の四角形を固定した実際の制限 fiber は同時端点条件の fiber と同型。
方針：任意のパラメーターでの条件の同値を fiber 同型へ移す。
規約：表現条件と充填性は不要。
使われ方：実際の境界表現を固定した fiber の可縮性。 -/
def intervalSquareRestrictionFiberIso {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1}))
    (S : LeftTransportSquare (pullback.snd p (boundary 1).ι)) :
    vertexFiber (transportSquareRestriction p (boundary 1).ι) (transportSquareVertex S) ≅
      vertexFiber (intervalSquareBoundaryConstraint p)
        (functorVertex (intervalMappingBoundary
          (S.diagram.app _ (intervalBoundaryVertex 0))
          (S.diagram.app _ (intervalBoundaryVertex 1))),
          functorVertex (intervalBoundaryPointedMap
            (S.intervalBoundaryFiberMap 0) (S.intervalBoundaryFiberMap 1))) :=
  vertexFiberIsoOfConstraintIff _ _ _ _ (fun _ F ↦ intervalSquareRestrictionCondition_iff p S F)

end SerrePositivity.InfinityCategories

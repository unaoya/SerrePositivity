module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalBoundaryFamilySquares

/-!
概要：区間の境界固定 lift 族を可換四角形の二つの境界条件の厳密な fiber と同定。
方針：分類図式の境界と全空間の両端を同時に制限し、普遍性で逆射を作る。
規約：分類区間内部は動かし両方の境界条件を固定する。
使われ方：表現の境界制限の実際の fiber との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可換四角形の底側と全空間側の境界を同時に制限する。
方針：分類図式の境界制限と二つの fiber の包含による制限を直積に束ねる。
規約：表現条件を課す前の全四角形の射。
使われ方：境界固定 lift の厳密な fiber 表示。 -/
def intervalSquareBoundaryConstraint {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) :=
  lift (transportSquareDiagram p ≫ (pre (boundary 1).ι).app SpaceInfinity)
    (transportSquarePointed p ≫ (pre (intervalFiberEndpointInclusion p)).app PointedSpaceInfinity)

/-- 概要：実際の区間族の全 lift 空間は二つの境界条件の同時 fiber と厳密に同型。
方針：分類区間の fiber と相対内部 Hom の引き戻しの普遍性で二方向の射を作る。
規約：両端写像の同値性も p の充填性も同型には要求しない。
使われ方：可縮性を表現空間の境界 fiber へ移す周囲の同型。 -/
def intervalFixedBoundaryFamilySquareFiberIso {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) :
    intervalFixedBoundaryFamilySpace p g₀ g₁ ≅
      vertexFiber (intervalSquareBoundaryConstraint p)
        (functorVertex (intervalMappingBoundary s t),
          functorVertex (intervalBoundaryPointedMap g₀ g₁)) := by
  let r := intervalBoundaryRelativeHom p
  let d := intervalFixedBoundaryFamilyData p g₀ g₁
  let S := intervalFixedBoundaryFamilySpace p g₀ g₁
  let cS := relativeBoundaryFamilyCurry r d
  let pS := relativeBoundaryFamilyProjection r d
  let m := intervalFixedBoundaryFamilySquareMap p g₀ g₁
  let ρ := intervalSquareBoundaryConstraint p
  let v := (functorVertex (intervalMappingBoundary s t),
    functorVertex (intervalBoundaryPointedMap g₀ g₁))
  let T := vertexFiber ρ v
  let ιT := vertexFiberι ρ v
  have hmρ : m ≫ ρ = SSet.const v := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ρ, v, Category.assoc, intervalSquareBoundaryConstraint, lift_fst, SSet.const_comp]
      rw [← Category.assoc, intervalFixedBoundaryFamilySquareMap_diagram, Category.assoc]
      change pS ≫ vertexFiberι ((pre (boundary 1).ι).app SpaceInfinity)
        (functorVertex (intervalMappingBoundary s t)) ≫ _ = _
      rw [vertexFiberι_comp, SSet.comp_const]
      rfl
    · simp only [ρ, v, Category.assoc, intervalSquareBoundaryConstraint, lift_snd, SSet.const_comp]
      rw [← Category.assoc, intervalFixedBoundaryFamilySquareMap_boundary]
      rfl
  let F : S ⟶ T := vertexFiberLift ρ v m hmρ
  have hF : F ≫ ιT = m := vertexFiberLift_ι _ _ _ _
  have hD : (ιT ≫ transportSquareDiagram p) ≫ (pre (boundary 1).ι).app SpaceInfinity =
      SSet.const (functorVertex (intervalMappingBoundary s t)) := by
    have h := congrArg (fun w ↦ w ≫ fst _ _) (vertexFiberι_comp ρ v)
    simp only [ρ, intervalSquareBoundaryConstraint, Category.assoc, lift_fst, SSet.const_comp] at h
    exact h
  have hP : (ιT ≫ transportSquarePointed p) ≫
      (pre (intervalFiberEndpointInclusion p)).app PointedSpaceInfinity =
      SSet.const (functorVertex (intervalBoundaryPointedMap g₀ g₁)) := by
    have h := congrArg (fun w ↦ w ≫ snd _ _) (vertexFiberι_comp ρ v)
    simp only [ρ, intervalSquareBoundaryConstraint, Category.assoc, lift_snd, SSet.const_comp] at h
    exact h
  let : Mono (cylinderIntervalDiagramι s t) :=
    inferInstanceAs (Mono (vertexFiberι ((pre (boundary 1).ι).app SpaceInfinity)
      (functorVertex (intervalMappingBoundary s t))))
  let b : T ⟶ intervalMappingSpace s t := vertexFiberLift _ _
    (ιT ≫ transportSquareDiagram p) hD
  have hb : b ≫ cylinderIntervalDiagramι s t = ιT ≫ transportSquareDiagram p :=
    vertexFiberLift_ι _ _ _ _
  have hG : (ιT ≫ transportSquarePointed p) ≫ r.π = b ≫ d := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc]
      change (ιT ≫ transportSquarePointed p) ≫ (pre (intervalFiberEndpointInclusion p)).app _ =
        b ≫ d ≫ r.fst
      dsimp only [d, intervalFixedBoundaryFamilyData, intervalBoundaryFamilyData]
      rw [relativeBoundaryFamilyData_fst, SSet.comp_const]
      exact hP
    · rw [Category.assoc, r.π_snd, Category.assoc]
      change (ιT ≫ transportSquarePointed p) ≫ (ihom E).map pointedSpaceProjection =
        b ≫ d ≫ r.snd
      dsimp only [d, intervalFixedBoundaryFamilyData, intervalBoundaryFamilyData]
      rw [relativeBoundaryFamilyData_snd, ← Category.assoc b, hb, Category.assoc]
      exact congrArg (fun w ↦ ιT ≫ w) (transportSquareSpace_condition p)
  let G : T ⟶ S := pullback.lift (ιT ≫ transportSquarePointed p) b hG
  have hG₀ : G ≫ cS = ιT ≫ transportSquarePointed p := pullback.lift_fst _ _ _
  have hG₁ : G ≫ pS = b := pullback.lift_snd _ _ _
  have hGm : G ≫ m = ιT := by
    apply pullback.hom_ext
    · change (G ≫ m) ≫ transportSquarePointed p = ιT ≫ transportSquarePointed p
      rw [Category.assoc, intervalFixedBoundaryFamilySquareMap_pointed]
      exact hG₀
    · change (G ≫ m) ≫ transportSquareDiagram p = ιT ≫ transportSquareDiagram p
      rw [Category.assoc, intervalFixedBoundaryFamilySquareMap_diagram, ← Category.assoc, hG₁]
      exact hb
  refine { hom := F, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · change (F ≫ G) ≫ cS = (𝟙 S) ≫ cS
      rw [Category.assoc, hG₀, ← Category.assoc, hF, Category.id_comp]
      exact intervalFixedBoundaryFamilySquareMap_pointed p g₀ g₁
    · change (F ≫ G) ≫ pS = (𝟙 S) ≫ pS
      apply (cancel_mono (cylinderIntervalDiagramι s t)).1
      simp only [Category.assoc, Category.id_comp]
      rw [← Category.assoc G pS, hG₁, hb, ← Category.assoc F ιT, hF]
      exact intervalFixedBoundaryFamilySquareMap_diagram p g₀ g₁
  · apply vertexFiber_hom_ext ρ v
    rw [Category.assoc, hF, hGm, Category.id_comp]

/-- 概要：同値な両端写像を固定した可換四角形の二つの境界条件の fiber は可縮。
方針：実際の区間族の可縮性を厳密な fiber 同型で移す。
規約：底の分類図式と全空間の射を同時に固定する。
使われ方：実際の表現空間の境界 fiber の可縮性の入力。 -/
lemma intervalSquareBoundaryConstraintFiber_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s) (h₀ : IsQCatEquivalence g₀)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) (h₁ : IsQCatEquivalence g₁) :
    IsContractibleKan (vertexFiber (intervalSquareBoundaryConstraint p)
      (functorVertex (intervalMappingBoundary s t),
        functorVertex (intervalBoundaryPointedMap g₀ g₁))) :=
  isContractibleKan_of_iso (intervalFixedBoundaryFamilySquareFiberIso p g₀ g₁)
    (intervalFixedBoundaryFamilySpace_isContractibleKan p g₀ h₀ g₁ h₁)

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.KST.LocalizingInvariants.FixedFractionEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalIsoHomClass

/-!
概要：固定端点の区間写像空間の全族を、関手圏の固定端点写像空間へ移す。
方針：二重内部 Hom の交換と、元の境界図式上の厳密 fiber の普遍性を使う。
規約：頂点や π₀ だけでなく、全高次単体と元の両端点を保持する。
使われ方：分数評価の比較族をパラメータ関手圏の同じ辺の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 定値図式の全族を転置すると、同じ図式の定値関手への後合成となる。 -/
lemma spanInternalHomFlip_const {K L X : SSet.{u}} (f : L ⟶ X) :
    internalHomFlipHomEquiv K L X (SSet.const (functorVertex f)) =
      f ≫ curry (snd K X) := by
  apply uncurry_injective
  change uncurry (curry ((β_ K L).hom ≫
    uncurry (SSet.const (functorVertex f)))) = _
  rw [uncurry_curry, uncurry_const_functorVertex,
    uncurry_natural_left, uncurry_curry]
  rfl

/-- 転置した固定境界は、関手圏の同じ二つの定値図式上の固定境界そのもの。 -/
lemma spanIntervalBoundaryFamily_flip (K X : SSet.{u}) (x y : X _⦋0⦌) :
    internalHomFlipHomEquiv K (boundary 1 : SSet.{u}) X
      (SSet.const (functorVertex (intervalMappingBoundary x y))) =
      intervalMappingBoundary (functorVertex (SSet.const x : K ⟶ X))
        (functorVertex (SSet.const y : K ⟶ X)) := by
  rw [spanInternalHomFlip_const]
  exact intervalMappingBoundary_postcomp (curry (snd K X)) x y

/-- 転置した関手辺の各成分は、元の全辺族の同じ一次単体。 -/
lemma spanInternalHomFlip_interval_edge {K X : SSet.{u}}
    (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (k : K _⦋0⦌) :
    (evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] X f)) =
      intervalFunctorVertexEdge (f.app (Opposite.op ⦋0⦌) k) := by
  let v := functorVertex (internalHomFlipHomEquiv K Δ[1] X f)
  have hs : (internalHomSwapIso Δ[1] K X).hom.app (Opposite.op ⦋0⦌) v =
      functorVertex f := by
    rw [internalHomSwapIso_functorVertex]
    change functorVertex ((internalHomFlipHomEquiv K Δ[1] X).symm
      ((internalHomFlipHomEquiv K Δ[1] X) f)) = _
    rw [Equiv.symm_apply_apply]
  have he := internalHomSwapIso_interval_evaluate K X v k
  rw [hs, evaluateFunctorAt_functorVertex] at he
  simpa only [v, intervalFunctorVertexEdge_functorVertex] using he.symm

/-- 固定端点 Hom の全族を、元のパラメータ関手圏の固定端点 Hom へ移す。 -/
def intervalMappingFamilyTranspose (K X : SSet.{u}) (x y : X _⦋0⦌) :
    (ihom K).obj (intervalMappingSpace x y) ⟶
      intervalMappingSpace (functorVertex (SSet.const x : K ⟶ X))
        (functorVertex (SSet.const y : K ⟶ X)) := by
  let p := (pre (boundary 1).ι).app X
  let b := functorVertex (intervalMappingBoundary x y)
  let a := (ihom K).map (vertexFiberι p b) ≫ (internalHomSwapIso K Δ[1] X).hom
  refine vertexFiberLift _ _ a ?_
  dsimp only [a]
  rw [Category.assoc, ← internalHomSwapIso_pre, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, vertexFiberι_comp, ihom_map_const,
    SSet.const_comp, internalHomSwapIso_functorVertex]
  change SSet.const (functorVertex
    (internalHomFlipHomEquiv K (boundary 1 : SSet.{u}) X
      (SSet.const (functorVertex (intervalMappingBoundary x y))))) = _
  rw [spanIntervalBoundaryFamily_flip]

/-- 全族の転置を元の辺関手に含めると、同じ内部 Hom の交換に一致する。 -/
lemma intervalMappingFamilyTranspose_inclusion (K X : SSet.{u}) (x y : X _⦋0⦌) :
    intervalMappingFamilyTranspose K X x y ≫
      vertexFiberι ((pre (boundary 1).ι).app ((ihom K).obj X))
        (functorVertex (intervalMappingBoundary (functorVertex (SSet.const x : K ⟶ X))
          (functorVertex (SSet.const y : K ⟶ X)))) =
      (ihom K).map (vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y))) ≫
        (internalHomSwapIso K Δ[1] X).hom := by
  unfold intervalMappingFamilyTranspose
  exact vertexFiberLift_ι _ _ _ _

/-- 固定端点の全族を、元のパラメータ関手圏の同じ両端点を持つ実辺として読む。 -/
def intervalMappingFamilyEdge {K X : SSet.{u}} {x y : X _⦋0⦌}
    (f : K ⟶ intervalMappingSpace x y) :
    SSet.Edge (functorVertex (SSet.const x : K ⟶ X))
      (functorVertex (SSet.const y : K ⟶ X)) :=
  intervalMappingEdgeOfVertex
    ((intervalMappingFamilyTranspose K X x y).app (Opposite.op ⦋0⦌) (functorVertex f))

/-- 回収した実辺の一次単体は、元の全族の厳密な転置の Yoneda 単体。 -/
lemma intervalMappingFamilyEdge_edge {K X : SSet.{u}} {x y : X _⦋0⦌}
    (f : K ⟶ intervalMappingSpace x y) :
    (intervalMappingFamilyEdge f).edge = SSet.yonedaEquiv
      (internalHomFlipHomEquiv K Δ[1] X (f ≫
        vertexFiberι ((pre (boundary 1).ι).app X)
          (functorVertex (intervalMappingBoundary x y)))) := by
  let v := (intervalMappingFamilyTranspose K X x y).app (Opposite.op ⦋0⦌) (functorVertex f)
  have hv : v.val = functorVertex (internalHomFlipHomEquiv K Δ[1] X
      (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y)))) := by
    have he := congrArg (fun g => g.app (Opposite.op ⦋0⦌) (functorVertex f))
      (intervalMappingFamilyTranspose_inclusion K X x y)
    change v.val = (internalHomSwapIso K Δ[1] X).hom.app (Opposite.op ⦋0⦌)
      (functorVertex (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y)))) at he
    exact he.trans (internalHomSwapIso_functorVertex K Δ[1] X _)
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] ((ihom K).obj X)).symm v.val) = _
  rw [hv]
  exact congrArg SSet.yonedaEquiv ((functorVertexEquiv Δ[1] ((ihom K).obj X)).symm_apply_apply _)

/-- 全族の関手同型は、パラメータ関手圏で回収した同じ実辺の Hom 類を一致させる。 -/
lemma intervalMappingFamilyEdge_homMk_eq {K X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f g : K ⟶ intervalMappingSpace x y} (e : FunctorIso f g) :
    Truncated.HomotopyCategory.homMk (intervalMappingFamilyEdge f).toTruncated =
      Truncated.HomotopyCategory.homMk (intervalMappingFamilyEdge g).toTruncated :=
  SerrePositivity.InfinityCategories.HomotopyLimits.intervalRecoveredHom_eq_of_vertexIso
    (VertexIso.map e (intervalMappingFamilyTranspose K X x y))

end SerrePositivity.KST.LocalizingInvariants

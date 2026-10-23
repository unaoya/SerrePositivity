module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：余錐形状の元の標準円柱を、底包含から右頂点へのホモトピーとして表示する。
方針：同じ join 円柱へ一点因子を補い、元の二端条件と全余錐での評価を回収する。
規約：元の円柱・全余錐の射を変更しない。
使われ方：全余錐間の変換の底と頂点の可換性を前合成の自然性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の余錐形状の底包含から、元の同じ右頂点への標準ホモトピー。 -/
def coconeDomainHomotopy (K : SSet.{u}) :
    SSet.Homotopy (joinInl K (Δ[0] : SSet.{u})) (SSet.const (coconeRightApexVertex K)) where
  h := pointTensorSection (K ⊗ (Δ[1] : SSet.{u})) ≫ joinCylinderMap K Δ[0]
  h₀ := by
    have h : SSet.ι₀ ≫ pointTensorSection (K ⊗ (Δ[1] : SSet.{u})) =
        pointTensorSection K ≫ (SSet.ι₀ ▷ (Δ[0] : SSet.{u})) := rfl
    rw [← Category.assoc, h, Category.assoc, joinCylinderMap_zero]
    rfl
  h₁ := by
    have h : SSet.ι₁ ≫ pointTensorSection (K ⊗ (Δ[1] : SSet.{u})) =
        pointTensorSection K ≫ (SSet.ι₁ ▷ (Δ[0] : SSet.{u})) := rfl
    rw [← Category.assoc, h, Category.assoc, joinCylinderMap_one]
    change (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫
      joinInr K Δ[0] = SSet.const (coconeRightApexVertex K)
    rw [SSet.const_comp]
    congr 1
    change (joinInr K Δ[0]).app (Opposite.op ⦋0⦌) _ = (joinInr K Δ[0]).app _ _
    congr 1
    apply stdSimplex.obj₀Equiv.injective
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 変換の一点パラメーターの円柱を元の辺のホモトピー円柱へ厳密に戻す。 -/
lemma constantTransformationPrism_point {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (t : (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) _⦋0⦌) :
    pointTensorSection (K ⊗ (Δ[1] : SSet.{u})) ≫
      F2.constantTransformationPrism (SSet.yonedaEquiv.symm t) =
        (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated).h := by
  obtain ⟨e, rfl⟩ := (intervalMappingEdgeVertexEquiv _ _).surjective t
  have he : (intervalMappingEdgeOfVertex
      ((intervalMappingEdgeVertexEquiv _ _) e)).edge = e.edge :=
    congrArg (fun a : SSet.Edge (functorVertex f) (functorVertex (SSet.const z)) ↦ a.edge)
      ((intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e)
  change _ = uncurry (SSet.yonedaEquiv.symm (intervalMappingEdgeOfVertex
    ((intervalMappingEdgeVertexEquiv _ _) e)).edge)
  rw [he]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 元の標準形状ホモトピーを指定余錐で写すと、同じ余錐の変換円柱そのもの。 -/
lemma coconeDomainHomotopy_postcomp {K X : SSet.{u}} {p : K ⟶ X} (q : JoinCocone p) :
    (functorHomotopyPostcomp (coconeDomainHomotopy K) q.val).h =
      (F2.coconeTransformationHomotopy q).h := by
  change (pointTensorSection (K ⊗ (Δ[1] : SSet.{u})) ≫ joinCylinderMap K Δ[0]) ≫ q.val = _
  rw [Category.assoc, ← F2.coconeTransformationVertex_prism, constantTransformationPrism_point]
  rfl

/-- 元の余錐で写した形状円柱の代表辺は、元の同じ余錐変換の代表辺。 -/
lemma coconeDomainHomotopy_postcomp_edge {K X : SSet.{u}} {p : K ⟶ X} (q : JoinCocone p) :
    (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coconeDomainHomotopy K) q.val)).edge =
        (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q)).edge := by
  have h := congrArg (fun f : K ⊗ (Δ[1] : SSet.{u}) ⟶ X ↦ SSet.yonedaEquiv (curry f))
    (coconeDomainHomotopy_postcomp q)
  refine h.trans ?_
  change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm
    (intervalMappingEdgeOfVertex (F2.coconeTransformationVertex q)).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HomotopyLimits

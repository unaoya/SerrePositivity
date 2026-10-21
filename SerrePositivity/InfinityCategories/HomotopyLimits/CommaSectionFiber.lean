module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaSectionUnit
public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaFiberRepresentative

/-!
概要：元の comma 切断の成分を始域・標的の二重 fiber で表示する。
方針：切断条件と標的の値で正規化し、単位の同じ円柱の辺を回収する。
規約：元の切断の点を保持。使われ方：単位の代表の変更と普遍性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の切断の点を、同じ始域 x 上の comma の点として保持。 -/
def commaSectionFiberVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) (x : X _⦋0⦌) :
    (unitCommaFiber G x) _⦋0⦌ :=
  ⟨s.app (Opposite.op ⦋0⦌) x, by
    rw [pinchedConstant_zero]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) x⟩

/-- 元の切断の成分を、同じ標的 F(x) 上の二重 fiber の点として保持。 -/
def commaSectionTargetFiberVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) (x : X _⦋0⦌) :
    (vertexFiber (F1B.kanUnitCommaFiberProjection G x)
      ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  ⟨commaSectionFiberVertex G s hs x, (pinchedConstant_zero _).symm⟩

/-- 二重 fiber から回収した辺は、元の切断の単位円柱の頂点辺そのもの。 -/
lemma commaSectionTargetFiberArrow_eq {X Y : SSet.{u}} (G : Y ⟶ X)
    (s : X ⟶ unitComma G) (hs : s ≫ unitCommaSource G = 𝟙 X) (x : X _⦋0⦌) :
    commaTargetFiberArrow G x ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
      (commaSectionTargetFiberVertex G s hs x) =
      simplicialHomotopyVertexEdge (commaSectionUnitHomotopy G s hs) x := by
  apply SSet.Edge.ext
  let v := commaSectionTargetFiberVertex G s hs x
  let k := F1B.kanUnitCommaFiberToInterval G x
    ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x)
  have he := intervalMappingVertexOfEdge_uncurry (intervalMappingEdgeOfVertex (k.app _ v))
  rw [show intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex (k.app _ v)) =
    k.app _ v from (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply _] at he
  rw [← SSet.yonedaEquiv_symm_comp, intervalMappingUncurry_precomp,
    F1B.kanUnitCommaFiberToInterval_uncurry] at he
  rw [← unitCommaUncurry_precomp] at he
  have hr : SSet.yonedaEquiv.symm v ≫
      (vertexFiberι (F1B.kanUnitCommaFiberProjection G x)
        ((s ≫ unitCommaTarget G).app (Opposite.op ⦋0⦌) x) ≫
          vertexFiberι (unitCommaSource G) x) = SSet.yonedaEquiv.symm x ≫ s := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  rw [hr, unitCommaUncurry_precomp] at he
  have hv := congrArg (fun f : (Δ[1] : SSet.{u}) ⊗ Δ[0] ⟶ X ↦
    f.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) 1)) he
  have hraw : (unitCommaUncurry s).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1) =
      (intervalMappingEdgeOfVertex (k.app _ v)).edge := by
    change (unitCommaUncurry s).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        (SSet.yonedaEquiv.symm x).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) 1)) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm
        (intervalMappingEdgeOfVertex (k.app _ v)).edge) at hv
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_symm_zero] at hv
    exact hv
  change (intervalMappingEdgeOfVertex (k.app _ v)).edge =
    (unitCommaUncurry s).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, (Truncated.Edge.id (X := (truncation 2).obj X) x).edge)
  rw [← hraw]
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [pinchedConstant_one, hi]

end SerrePositivity.InfinityCategories.HomotopyLimits

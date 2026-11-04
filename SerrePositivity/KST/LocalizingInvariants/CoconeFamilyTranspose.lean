module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeVertexTriangles
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingFamilyTranspose
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.SimplexTerminalCoconeExtension

/-!
概要：同じ前段上の全余錐族を、パラメータ関手圏の元の全余錐へ移す。
方針：内部 Hom の厳密転置で前段と終端脚を保ち、比較同型も同じ交換で移す。
規約：終端脚は元の実辺の一次単体のまま回収する。
使われ方：回収した実分母・次辺を指定前段経路付きの全単体比較へ貼る。
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

/-- 前段が同じ図式に厳密に定値な余錐族を、関手圏の元の余錐へ移す。 -/
def spanCoconeFamilyTranspose {K L X : SSet.{u}} (D : L ⟶ X)
    (F : K ⟶ (ihom (join L (Δ[0] : SSet.{u}))).obj X)
    (hF : F ≫ (pre (joinInl L Δ[0])).app X = SSet.const (functorVertex D)) :
    JoinCocone (D ≫ curry (snd K X)) :=
  ⟨internalHomFlipHomEquiv K (join L Δ[0]) X F, by
    rw [← internalHomFlipHomEquiv_pre_app, hF, spanInternalHomFlip_const]⟩

/-- 同じ終端辺の全族から、転置した元の余錐の同じ終端脚を厳密に回収する。 -/
lemma spanCoconeFamilyTranspose_last_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (functorVertex D))
    (a : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (ha : F ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X =
      a ≫ (pre (joinStdSimplexIso 0 0).hom).app X) :
    (SerrePositivity.InfinityCategories.HomotopyLimits.coconeVertexLeg
      (spanCoconeFamilyTranspose D F hF) (SSet.yonedaEquiv (simplexLastPoint n))).edge =
      SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] X a) := by
  have he := congrArg (internalHomFlipHomEquiv K (join (Δ[0] : SSet.{u}) Δ[0]) X) ha
  rw [internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre_app] at he
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (simplexLastPoint n))) (𝟙 Δ[0]) ≫
      internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) X F) = _
  rw [Equiv.symm_apply_apply, he,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 元の固定端点 Hom の族で指定した終端脚を、同じ実関手辺として回収する。 -/
lemma spanCoconeFamilyTranspose_last_interval_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (functorVertex D)) {x y : X _⦋0⦌}
    (f : K ⟶ intervalMappingSpace x y)
    (hf : F ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X =
      f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y)) ≫
        (pre (joinStdSimplexIso 0 0).hom).app X) :
    (HomotopyLimits.coconeVertexLeg (spanCoconeFamilyTranspose D F hF)
      (SSet.yonedaEquiv (simplexLastPoint n))).edge = (intervalMappingFamilyEdge f).edge := by
  have he := spanCoconeFamilyTranspose_last_edge D F hF
    (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))) hf
  exact he.trans (intervalMappingFamilyEdge_edge f).symm

end SerrePositivity.KST.LocalizingInvariants

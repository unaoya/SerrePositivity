module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSource
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：固定始域の閉包内 coslice の全単体を、元の飽和射圏へ送る。
方針：全余錐族を一点と一点の join 同型で制限し、元の脚の所属で持ち上げる。
規約：頂点だけの選択から関手を作らず、元の coherent な余錐族を保持する。
使われ方：固定始域圏と飽和射圏の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の全 coslice の余錐族を、そのまま元の射の族へ制限する。 -/
def sourceCosliceArrowFamily (x : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm x) ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C :=
  nativeCoconeFunctorFamily (SSet.yonedaEquiv.symm x) ≫
    (pre (joinStdSimplexIso 0 0).inv).app C

omit [Quasicategory C] in
/-- 制限した射族の各頂点は、元の同じ余錐の指定脚である。 -/
lemma sourceCosliceArrowFamily_vertex (x : C _⦋0⦌)
    (c : JoinCocone (SSet.yonedaEquiv.symm x)) :
    arrowVertexEdge ((sourceCosliceArrowFamily x).app _ c) =
      (JoinCocone.leg c (𝟙 Δ[0])).edge := by
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] C).symm
    (((pre (joinStdSimplexIso 0 0).inv).app C).app _
      ((nativeCoconeFunctorFamily (SSet.yonedaEquiv.symm x)).app _ c))) = _
  rw [nativeCoconeFunctorFamily_vertex, functorVertexMap_precomp]
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ c.val) =
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ c.val)
  rw [joinMap_id, Category.id_comp]

/-- 元の coherent な脚の族を、飽和射の全部分圏へ送る。 -/
def generatedSourceArrows (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceCategory edges x ⟶ generatedArrowCategory edges :=
  fullSubcomplexLift _ (generatedSourceInclusion edges x ≫ sourceCosliceArrowFamily x)
    (fun c ↦ by
      change arrowVertexEdge ((sourceCosliceArrowFamily x).app _ c.val) ∈ _
      rw [sourceCosliceArrowFamily_vertex]
      exact fullSubcomplexOnVertices_vertex c)

/-- 射圏への比較は、元の余錐族から作った同じ全単体の射を回収する。 -/
lemma generatedSourceArrows_inclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrows edges x ≫ generatedArrowInclusion edges =
      generatedSourceInclusion edges x ≫ sourceCosliceArrowFamily x :=
  fullSubcomplexLift_ι _ _ _

omit [Quasicategory C] in
/-- 元の脚の族の終点評価は、元の coslice 射影そのもの。 -/
lemma sourceCosliceArrowFamily_target (x : C _⦋0⦌) :
    sourceCosliceArrowFamily x ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  have he : (joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = coconeRightApexVertex Δ[0] := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp]
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i
      rfl
    rw [hv]
    change _ = SSet.yonedaEquiv.symm ((joinInr Δ[0] Δ[0]).app _
      (SSet.yonedaEquiv (𝟙 Δ[0])))
    rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.id_comp]
    rw [← joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [sourceCosliceArrowFamily, Category.assoc, evaluateFunctorAt_pre, he,
    nativeCoconeFunctorFamily_apex]

/-- 飽和射圏への比較の終点は、元の固定始域圏の終域射影に厳密に一致する。 -/
lemma generatedSourceArrows_target (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrows edges x ≫ generatedArrowInclusion edges ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = generatedSourceTarget edges x := by
  rw [← Category.assoc, generatedSourceArrows_inclusion, Category.assoc,
    sourceCosliceArrowFamily_target]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization

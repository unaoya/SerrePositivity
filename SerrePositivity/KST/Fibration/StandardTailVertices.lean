module
public import SerrePositivity.KST.Fibration.StandardTailAttachment

/-! # 貼り合わせの共有端点と最後の辺の元の頂点座標 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 先行標準単体の共有端点は、元の標準 join の右端の零単体。 -/
lemma standardTailEndpoint_join (n : ℕ) :
    standardTailEndpoint.{u} n = joinInr (Δ[n] : SSet.{u}) Δ[0] ≫
      (joinStdSimplexIso n 0).hom := by
  change initialHornPointIso.hom ≫ joinInr _ _ ≫
    (joinMap (𝟙 _) initialHornPointIso.inv ≫ (joinStdSimplexIso n 0).hom) = _
  rw [joinInr_joinMap_assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 最後の辺の包含後は、元の標準 join の右因子の包含を回収する。 -/
lemma standardTailEdge_inclusion (n : ℕ) :
    tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ standardTailInclusion n =
      joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso n 1).hom := by
  have he : tailAttachmentEdge (Δ[n] : SSet.{u}) ≫
      (tailAttachment (Δ[n] : SSet.{u})).ι = joinInr (Δ[n] : SSet.{u}) Δ[1] := by
    change ((emptyJoinIso (Δ[n] : SSet.{u}) Δ[1]).inv ≫
      joinUnionLeft (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0)) ≫
        (joinUnion (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0)).ι = _
    rw [Category.assoc, joinUnionLeft_ι]
    change joinInr _ _ ≫ joinMap (⊥ : (Δ[n] : SSet.{u}).Subcomplex).ι (𝟙 _) = _
    rw [joinInr_joinMap, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans (congrArg
    (fun f => f ≫ (joinStdSimplexIso n 1).hom) he)

/-- 元の標準 join の右因子の頂点座標は、左因子の全頂点数だけずれる。 -/
lemma joinStdSimplexIso_inr_vertex (n m : ℕ) (j : Fin (m + 1)) :
    ((joinInr (Δ[n] : SSet.{u}) Δ[m] ≫ (joinStdSimplexIso n m).hom).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) =
        stdSimplex.obj₀Equiv.symm ⟨n + 1 + j.val, by omega⟩ := by
  apply stdSimplex.ext
  intro a
  apply Fin.ext
  rfl

/-- 共有端点は元の先行標準単体の最後の頂点そのもの。 -/
lemma standardTailEndpoint_vertex (n : ℕ) :
    (standardTailEndpoint.{u} n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
        stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)) := by
  rw [standardTailEndpoint_join, joinStdSimplexIso_inr_vertex]
  apply congrArg stdSimplex.obj₀Equiv.symm
  apply Fin.ext
  simp

/-- 共有端点の全単体の射は、元の先行標準単体の最後の頂点の Yoneda 表示と一致する。 -/
lemma standardTailEndpoint_eq_yoneda (n : ℕ) :
    standardTailEndpoint.{u} n =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact standardTailEndpoint_vertex n

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingSurjective
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowCommonPresentation

/-!
概要：基底射列の全射表示へ同じ係数を戻し、退化作用素の単射性を確認する。
方針：始点の等式の移送を打ち消し、全射の分裂を同じ行の関手で運ぶ。
規約：元の退化作用素とその元の係数の単体を保持する。
使われ方：IS-W2 R03f.2のlatching余錐の一意性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ全射作用素による行の退化は、分裂単射の像なので単射である。 -/
theorem simplicialReplacementRowReindex_mono {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    Mono (simplicialReplacementRowReindex F α) := by
  haveI : IsSplitEpi α := isSplitEpi_of_epi α
  change Mono ((simplicialReplacementRows F).map α.op)
  infer_instance

/-- 元の基底の全射表示に、元の同じ係数の単体を厳密に戻せる。 -/
theorem simplicialReplacementRowReindex_lift {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (τ : ComposableArrows I n.len) (q : SimplexCategoryᵒᵖ)
    (x : (simplicialReplacementRow F m.len).obj q)
    (h : (nerve I).map α.op τ = x.1) :
    ∃ y : (F.obj (τ.obj 0)).obj q,
      (simplicialReplacementRowReindex F α).app q ⟨τ,y⟩ = x := by
  rcases x with ⟨σ,x⟩
  dsimp only at h
  subst σ
  have e : F.obj (τ.obj (α.toOrderHom 0)) = F.obj (τ.obj 0) :=
    congrArg (fun k => F.obj (τ.obj k)) (simplicialReplacement_epi_zero α)
  refine ⟨(eqToHom e).app q x, ?_⟩
  refine Sigma.ext (show α.toOrderHom.monotone.functor ⋙ τ = (nerve I).map α.op τ from rfl) ?_
  apply heq_of_eq
  change (F.map (τ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))).app q
    ((eqToHom e).app q x) = x
  rw [simplicialReplacement_epi_coefficient]
  change ((eqToHom e ≫ eqToHom e.symm).app q) x = x
  rw [eqToHom_trans]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

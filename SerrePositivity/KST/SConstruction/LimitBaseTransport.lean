module
public import SerrePositivity.InfinityCategories.Stable.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Core.ConeRestrictionCocartesianFibration
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian

/-! # 可逆な図式の辺に沿う極限の存在
概要：極限錐は可逆な図式の辺に沿って輸送できる。
方針：錐の cocartesian 輸送を可逆な全錐の辺にし、相対終点境界充填を移す。
規約：coherent な関手同型を使う。使われ方：HTT §4.3.2、固定零射の cofiber の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：普遍錐の頂点は、可逆な基底の辺に沿い厳密に持ち上がる。
方針：cocartesian な錐の辺を選び、基底での可逆性から全体の可逆性を得る。
規約：K は任意、X は quasicategory。使われ方：図式の同型による極限存在の輸送。 -/
lemma exists_terminalConeVertex_over_invertible_edge (K X : SSet.{u}) [Quasicategory X]
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌)
    (hv : TerminalBoundaryLifting (coneRestriction K X) v)
    (b : ((ihom K).obj X) _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      ((coneRestriction K X).app (Opposite.op ⦋0⦌) v) b) (he : IsInvertibleEdge e) :
    ∃ w : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌,
      (coneRestriction K X).app (Opposite.op ⦋0⦌) w = b ∧
        TerminalBoundaryLifting (coneRestriction K X) w := by
  obtain ⟨w, f, hf, hcart⟩ := CocartesianHornFibration.exists_lift
    (p := coneRestriction K X) v b e
  have hfm : IsInvertibleEdge (X := (ihom K).obj X) (f.map ((truncation 2).map (coneRestriction K X))) :=
    (isInvertibleEdge_congr (X := (ihom K).obj X)
      (e := f.map ((truncation 2).map (coneRestriction K X))) (f := e) hf).2 he
  have hfi : IsInvertibleEdge f := hcart.isInvertibleEdge_of_map hfm
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk f) := hfi
  have hi : VertexIso v w := asIso (SSet.Truncated.HomotopyCategory.homMk f)
  refine ⟨w, ?_, TerminalBoundaryLifting.of_vertexIso (coneRestriction K X) hv hi⟩
  have hs := (f.map ((truncation 2).map (coneRestriction K X))).tgt_eq
  exact hs.symm.trans ((congrArg (((ihom K).obj X).δ 0) hf).trans e.tgt_eq)

/-- 概要：coherent に同型な図式の一方に極限があれば他方にも存在する。
方針：同型を辺で表し、既存の普遍錐を cocartesian に輸送して実際の新しい錐を作る。
規約：基底図式への制限は同型でなく厳密な等号である。
使われ方：任意の指定零射を持つ cospan への fiber の存在の移送。 -/
lemma HasLimit.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (hq : HasLimit q) (e : FunctorIso p q) : HasLimit p := by
  obtain ⟨c, hc⟩ := hq
  let r := coneRestriction K X
  let v := functorVertex c.val
  have hv : r.app (Opposite.op ⦋0⦌) v = functorVertex q := by
    change functorVertex (joinInr Δ[0] K ≫ c.val) = _
    rw [c.property]
  let er : FunctorIso q p := e.symm
  let f := er.edge
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (r.app (Opposite.op ⦋0⦌) v) (functorVertex p) :=
    ⟨f.edge, f.src_eq.trans hv.symm, f.tgt_eq⟩
  have hi : IsInvertibleEdge f' :=
    (isInvertibleEdge_congr (e := f') (f := f) rfl).2 er.edge_isInvertible
  obtain ⟨w, hw, hwi⟩ := exists_terminalConeVertex_over_invertible_edge K X v
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc) (functorVertex p) f' hi
  let W := (functorVertexEquiv (join (Δ[0] : SSet.{u}) K) X).symm w
  have hW : functorVertex W = w := (functorVertexEquiv _ X).apply_symm_apply _
  have hWp : joinInr (Δ[0] : SSet.{u}) K ≫ W = p := by
    apply functorVertex_injective
    have hh := (congrArg (fun z => r.app (Opposite.op ⦋0⦌) z) hW).trans hw
    exact hh
  let d : JoinCone p := ⟨W, hWp⟩
  refine ⟨d, ?_⟩
  apply isLimitCone_of_terminalBoundaryLifting_coneRestriction d
  exact hW.symm ▸ hwi

/-- 概要：同型な図式の極限の存在は同値。
方針：同型と逆同型を使う。
規約：X は quasicategory。使われ方：零頂点や零射の選択の変更。 -/
lemma hasLimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) : HasLimit p ↔ HasLimit q :=
  ⟨fun h => HasLimit.of_functorIso h e.symm,
    fun h => HasLimit.of_functorIso h e⟩

end SerrePositivity.KST.SConstruction

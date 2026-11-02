module
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport
public import SerrePositivity.InfinityCategories.F1.CoconeCartesianTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian

/-! # 可逆な図式の辺に沿う余極限の存在
概要：余極限余錐は可逆な図式の辺に沿って輸送できる。
方針：余錐の cartesian 輸送を可逆な全余錐の辺にし、相対始点境界充填を移す。
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

/-- 概要：普遍余錐の頂点は、可逆な基底の辺に沿い厳密に持ち上がる。
方針：cartesian な余錐の辺を選び、基底での可逆性から全体の可逆性を得る。
規約：K は任意、X は quasicategory。使われ方：図式の同型による余極限存在の輸送。 -/
lemma exists_initialCoconeVertex_over_invertible_edge (K X : SSet.{u}) [Quasicategory X]
    (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌)
    (hv : InitialBoundaryLifting (coconeRestriction K X) v)
    (b : ((ihom K).obj X) _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) b
      ((coconeRestriction K X).app (Opposite.op ⦋0⦌) v)) (he : IsInvertibleEdge e) :
    ∃ w : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌,
      (coconeRestriction K X).app (Opposite.op ⦋0⦌) w = b ∧
        InitialBoundaryLifting (coconeRestriction K X) w := by
  obtain ⟨w, f, hf, hcart⟩ := exists_cartesian_cocone_lift K X v b e
  have hfm : IsInvertibleEdge (X := (ihom K).obj X) (f.map ((truncation 2).map (coconeRestriction K X))) :=
    (isInvertibleEdge_congr (X := (ihom K).obj X) (e := f.map ((truncation 2).map (coconeRestriction K X)))
      (f := e) hf).2 he
  have hfi : IsInvertibleEdge f :=
    isInvertibleEdge_of_isCartesianEdge (coconeRestriction K X) f hcart hfm
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk f) := hfi
  have hi : VertexIso w v := asIso (SSet.Truncated.HomotopyCategory.homMk f)
  refine ⟨w, ?_, InitialBoundaryLifting.of_vertexIso (coconeRestriction K X) hv hi.symm⟩
  have hs := (f.map ((truncation 2).map (coconeRestriction K X))).src_eq
  exact hs.symm.trans ((congrArg (((ihom K).obj X).δ 1) hf).trans e.src_eq)

/-- 概要：coherent に同型な図式の一方に余極限があれば他方にも存在する。
方針：同型を辺で表し、既存の普遍余錐を cartesian に輸送して実際の新しい余錐を作る。
規約：基底図式への制限は同型でなく厳密な等号である。
使われ方：任意の指定零射を持つ span への cofiber の存在の移送。 -/
lemma HasColimit.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (hq : HasColimit q) (e : FunctorIso p q) : HasColimit p := by
  obtain ⟨c, hc⟩ := hq
  let r := coconeRestriction K X
  let v := functorVertex c.val
  have hv : r.app (Opposite.op ⦋0⦌) v = functorVertex q := by
    change functorVertex (joinInl K Δ[0] ≫ c.val) = _
    rw [c.property]
  let f := e.edge
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (functorVertex p) (r.app (Opposite.op ⦋0⦌) v) :=
    ⟨f.edge, f.src_eq, f.tgt_eq.trans hv.symm⟩
  have hi : IsInvertibleEdge f' :=
    (isInvertibleEdge_congr (e := f') (f := f) rfl).2 e.edge_isInvertible
  obtain ⟨w, hw, hwi⟩ := exists_initialCoconeVertex_over_invertible_edge K X v
    hc.initialBoundaryLifting (functorVertex p) f' hi
  let W := (functorVertexEquiv (join K (Δ[0] : SSet.{u})) X).symm w
  have hW : functorVertex W = w := (functorVertexEquiv _ X).apply_symm_apply _
  have hWp : joinInl K (Δ[0] : SSet.{u}) ≫ W = p := by
    apply functorVertex_injective
    have hh := (congrArg (fun z => r.app (Opposite.op ⦋0⦌) z) hW).trans hw
    exact hh
  let d : JoinCocone p := ⟨W, hWp⟩
  refine ⟨d, ?_⟩
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction d
  exact hW.symm ▸ hwi

/-- 概要：同型な図式の余極限の存在は同値。
方針：同型と逆同型を使う。
規約：X は quasicategory。使われ方：零頂点や零射の選択の変更。 -/
lemma hasColimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) : HasColimit p ↔ HasColimit q :=
  ⟨fun h => HasColimit.of_functorIso h e.symm,
    fun h => HasColimit.of_functorIso h e⟩

end SerrePositivity.KST.SConstruction

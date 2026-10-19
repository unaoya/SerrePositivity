module

public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.KanJoinPrismFixed
public import SerrePositivity.InfinityCategories.Stable.CoconeFamily

/-!
概要：図式を全時間固定する可逆な円柱を固定図式上の余錐の同型にする。
方針：円柱の curry を余錐制限の頂点 fiber へ持ち上げ、可逆性を fiber 内へ反映する。
規約：余錐全体の同型だけでなく、図式固定の余錐の族の同型を得る。
使われ方：標準底余錐と普遍 comma 底余錐を固定図式上で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆な円柱が図式を固定すると余錐の族の中で両端を同型にする。
方針：時間を交換して関手圏の辺を作り、固定条件で fiber へ持ち上げる。
規約：P の垂直辺は全頂点で可逆とする。
使われ方：底の余錐の比較を元の図式を変えずに持ち上げる。 -/
def kanCoconeFamilyPrismIso {K D : SSet.{u}} [Quasicategory D]
    {p : K ⟶ D} (c d : JoinCocone p)
    (P : (Δ[1] : SSet.{u}) ⊗ join K (Δ[0] : SSet.{u}) ⟶ D)
    (hfixed : (Δ[1] ◁ joinInl K (Δ[0] : SSet.{u})) ≫ P = snd Δ[1] K ≫ p)
    (h₀ : prismEndpoint 0 _ ≫ P = c.val) (h₁ : prismEndpoint 1 _ ≫ P = d.val)
    (hi : ∀ x : (join K (Δ[0] : SSet.{u})) _⦋0⦌,
      IsInvertibleEdge (edgeOfSimplex (P.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    VertexIso (coconeFamilyVertexEquiv p c) (coconeFamilyVertexEquiv p d) := by
  let T := join K (Δ[0] : SSet.{u})
  let H : SSet.Homotopy c.val d.val := {
    h := (β_ T (Δ[1] : SSet.{u})).hom ≫ P
    h₀ := by change prismEndpoint 0 T ≫ P = _; exact h₀
    h₁ := by change prismEndpoint 1 T ≫ P = _; exact h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have hf : curry H.h ≫ coconeRestriction K D = SSet.const (functorVertex p) := by
    apply uncurry_injective
    rw [coconeRestriction, uncurry_pre_app, uncurry_curry, uncurry_const_functorVertex]
    change (joinInl K (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      ((β_ T (Δ[1] : SSet.{u})).hom ≫ P) = fst K Δ[1] ≫ p
    calc
      _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
          ((Δ[1] ◁ joinInl K (Δ[0] : SSet.{u})) ≫ P) := rfl
      _ = _ := by rw [hfixed]; rfl
  let a := vertexFiberLift (coconeRestriction K D) (functorVertex p) (curry H.h) hf
  let e := edgeOfSimplex (SSet.yonedaEquiv a)
  have he₀ : (coconeFamily p).δ 1 (SSet.yonedaEquiv a) = coconeFamilyVertexEquiv p c := by
    apply Subtype.ext
    change ((ihom T).obj D).δ 1 (SSet.yonedaEquiv (curry H.h)) = functorVertex c.val
    rw [← functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry, H.h₀]
  have he₁ : (coconeFamily p).δ 0 (SSet.yonedaEquiv a) = coconeFamilyVertexEquiv p d := by
    apply Subtype.ext
    change ((ihom T).obj D).δ 0 (SSet.yonedaEquiv (curry H.h)) = functorVertex d.val
    rw [← functorVertex_uncurry_one, Equiv.symm_apply_apply, uncurry_curry, H.h₁]
  have hH : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
    apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H
    intro x
    have hv := hi x
    have he : (simplicialHomotopyVertexEdge H x).edge =
        P.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1) := by
      change P.app (Opposite.op ⦋1⦌)
        (homotopyIntervalEdge.edge,
          (SSet.Truncated.Edge.id (X := (truncation 2).obj T) x).edge) = _
      have he : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro j
        fin_cases j <;> rfl
      rw [← pinchedConstant_one, he]
    exact (isInvertibleEdge_congr he).2 hv
  have hie : IsInvertibleEdge e := by
    apply (isInvertibleEdge_vertexFiber_iff (coconeRestriction K D) (functorVertex p) e).2
    exact (isInvertibleEdge_congr (e := functorEdgeOfSimplicialHomotopy H) (f :=
      e.map ((truncation 2).map (vertexFiberι (coconeRestriction K D) (functorVertex p))))
      rfl).1 hH
  exact eqToIso (congrArg (fun v ↦ HomotopyCategory.mk v) he₀.symm) ≪≫
    asIso (SSet.Truncated.HomotopyCategory.homMk e) ≪≫
      eqToIso (congrArg (fun v ↦ HomotopyCategory.mk v) he₁)

end SerrePositivity.InfinityCategories.F1B

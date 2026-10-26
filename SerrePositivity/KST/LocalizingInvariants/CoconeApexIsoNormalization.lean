module

public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：全前段を固定したまま、余錐頂点を指定した同型の始点に厳密に揃える。
方針：coslice 射影の left fibration で指定可逆辺を持ち上げ、全余錐の同型へ戻す。
規約：全前段の固定と全余錐の FunctorIso を保持し、頂点だけの比較で代用しない。
使われ方：c5 の全図式持ち上げで商の像に属する余錐頂点へ正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 前段全体を固定し、頂点を指定点に厳密に揃えた同型な実余錐を構成する。 -/
lemma exists_cocone_apexIsoNormalization {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (c : JoinCocone F) {z : X _⦋0⦌} (e : VertexIso z c.vertex) :
    ∃ d : JoinCocone F, d.vertex = z ∧ Nonempty (FunctorIso d.val c.val) := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective z c.vertex e.hom
  have hai : IsInvertibleEdge a := by
    rw [IsInvertibleEdge, ha]
    infer_instance
  let p := sliceUnderProjection F
  obtain ⟨L, hL₁, hLp⟩ := leftFibration_liftInvertibleEdge_target p c a hai
  let v := (sliceUnder F).δ 1 (SSet.yonedaEquiv L)
  let d : JoinCocone F := v
  let l : Truncated.Edge (X := (truncation 2).obj (sliceUnder F)) v c := {
    edge := SSet.yonedaEquiv L
    src_eq := rfl
    tgt_eq := by
      change (sliceUnder F).δ 0 (SSet.yonedaEquiv L) = c
      rw [← stdSimplex.yonedaEquiv_δ_comp, hL₁, Equiv.apply_symm_apply] }
  have hmap : (l.map ((truncation 2).map p)).edge = a.edge := by
    change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) = a.edge
    rw [← SSet.yonedaEquiv_comp, hLp]
    exact Equiv.apply_symm_apply _ _
  have hz : d.vertex = z := by
    change p.app (Opposite.op ⦋0⦌) ((sliceUnder F).δ 1 (SSet.yonedaEquiv L)) = z
    calc
      _ = X.δ 1 (p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L)) :=
        ConcreteCategory.congr_hom (C := Type u)
          (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) (SSet.yonedaEquiv L)
      _ = z := by
        change X.δ 1 (l.map ((truncation 2).map p)).edge = z
        rw [hmap]
        exact a.src_eq
  have hli : IsInvertibleEdge l :=
    leftFibration_reflects_invertibleEdge p l ((isInvertibleEdge_congr hmap).mpr hai)
  exact ⟨d, hz, ⟨coconeFunctorIsoOfVertexIso d c
    (asIso (Truncated.HomotopyCategory.homMk l))⟩⟩

end SerrePositivity.KST.LocalizingInvariants

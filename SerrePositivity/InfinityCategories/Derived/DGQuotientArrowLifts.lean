module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFractionTriangles
public import SerrePositivity.InfinityCategories.Derived.ArrowIsoFromCommutingEdges
/-!
概要：商の任意実辺は、元の実辺の像と区間上の全関手圏で同型。
方針：指定辺の実分数三角形を、可逆分母と恒等終点を持つ実可換正方形に読む。
規約：H⁰ の Arrow の同型だけでは済ませない。使われ方：商からの関手の完全性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 指定商対象を両端とする実辺は、元の同じ分数三角形の分子の像と全関手圏で同型。 -/
lemma dgQuotientEdge_exists_original_arrow_iso (P : Set D)
    (hP : DGQuotient.localKFlat A D P) {x y : D}
    (k : Truncated.Edge (X := (truncation 2).obj (dgQuotientNerve A D P))
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))) :
    ∃ b : (dgNerve A D) _⦋1⦌,
      Nonempty (FunctorIso (SSet.yonedaEquiv.symm b ≫ dgQuotientNerveProjection A D P)
        (SSet.yonedaEquiv.symm k.edge)) := by
  obtain ⟨z, d, g, _, hd, ⟨t⟩⟩ := dgQuotientEdge_exists_fractionTriangle A D P hP k
  let idY := Truncated.Edge.id (X := (truncation 2).obj (dgQuotientNerve A D P))
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))
  have hi : IsInvertibleEdge (X := dgQuotientNerve A D P) idY := by
    change IsIso (Truncated.HomotopyCategory.homMk idY)
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hc : Truncated.HomotopyCategory.homMk
      (dgClosedMappedEdge A D (DGQuotient.QuotientObject D P) (DGQuotient.inclusion A D P) g) ≫
      Truncated.HomotopyCategory.homMk idY =
        Truncated.HomotopyCategory.homMk
          (dgClosedMappedEdge A D (DGQuotient.QuotientObject D P)
            (DGQuotient.inclusion A D P) d) ≫ Truncated.HomotopyCategory.homMk k := by
    have hid : Truncated.HomotopyCategory.homMk idY = 𝟙 _ :=
      by
        dsimp only [idY]
        exact Truncated.HomotopyCategory.homMk_id _
    exact ((congrArg (fun v => Truncated.HomotopyCategory.homMk
      (dgClosedMappedEdge A D (DGQuotient.QuotientObject D P)
        (DGQuotient.inclusion A D P) g) ≫ v) hid).trans (Category.comp_id _)).trans
          (Truncated.HomotopyCategory.homMk_comp_homMk t).symm
  obtain ⟨e⟩ := nonempty_arrowFunctorIso_of_comm _ k _ idY hd hi hc
  refine ⟨g.edge, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  exact ⟨e⟩
/-- 商の任意の実一次単体は、元の実一次単体の像と区間上の全関手圏で同型。 -/
lemma dgQuotientNerveProjection_arrow_lifts (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (a : (dgQuotientNerve A D P) _⦋1⦌) :
    ∃ b : (dgNerve A D) _⦋1⦌,
      Nonempty (FunctorIso (SSet.yonedaEquiv.symm b ≫ dgQuotientNerveProjection A D P)
        (SSet.yonedaEquiv.symm a)) := by
  let e := edgeOfSimplex a
  let x := (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) ((dgQuotientNerve A D P).δ 1 a)
  let y := (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) ((dgQuotientNerve A D P).δ 0 a)
  have hx : Simplex.vertex x = (dgQuotientNerve A D P).δ 1 a :=
    (dgNerve.vertexEquiv A _).symm_apply_apply _
  have hy : Simplex.vertex y = (dgQuotientNerve A D P).δ 0 a :=
    (dgNerve.vertexEquiv A _).symm_apply_apply _
  let k : Truncated.Edge (X := (truncation 2).obj (dgQuotientNerve A D P))
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x.val))
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj y.val)) := {
    edge := a
    src_eq := hx.symm
    tgt_eq := hy.symm }
  exact dgQuotientEdge_exists_original_arrow_iso A D P hP k
end SerrePositivity.InfinityCategories

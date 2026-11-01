module

public import SerrePositivity.InfinityCategories.F1B.PinchedSliceCompositionRealization
public import SerrePositivity.InfinityCategories.F1B.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition

/-!
概要：元の選択済み Hom 前合成を、元の辺の全底を保つ実 slice 円柱で実現する。
方針：前合成の全族の仕様を、D から供給された合成円柱の存在へ渡す。
規約：D の二モジュールは許可された新規の葉からだけ読み取り専用 import する。
使われ方：表現可能前層の反対辺像の反転から、元の Hom の局所性を判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：同じ選択済み前合成は元の指定辺を底とする slice prism で実現できる。
方針：全関手圏の合成仕様を実円柱へ移す。
規約：同じ元の前合成と底辺。使われ方：輸送による局所性の反映。 -/
lemma pinchedPrecompose_slicePrism_exists {X : SSet.{u}} [Quasicategory X]
    (z : X _⦋0⦌) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ pinchedHom y z ⟶ sliceOver (SSet.yonedaEquiv.symm z),
      prismEndpoint 0 _ ≫ H =
        PinchedInterval.precompose z (Truncated.HomotopyCategory.homMk e) ≫
          pinchedFamilySlice X x z ∧
      prismEndpoint 1 _ ≫ H = pinchedFamilySlice X y z ∧
      H ≫ sliceOverProjection _ = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge := by
  let K := pinchedHom y z
  let s := (pinchedHomVertexEquiv x y).symm e
  let f : K ⟶ pinchedHom x y := SSet.const s
  let c := PinchedInterval.precompose z (Truncated.HomotopyCategory.homMk e)
  have hf : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) =
      constantFunctorHomMap K (Truncated.HomotopyCategory.homMk e) := by
    simpa only [f, s, Equiv.apply_symm_apply] using pinchedFamilyHom_const_vertex (K := K) s
  have hc := intervalFamilyHom_eq_of_homotopy (FunctorIso.simplicialHomotopy
    (PinchedInterval.liftMapComparisonIso
      (intervalPrecompose z (Truncated.HomotopyCategory.homMk e))))
  rw [intervalPrecompose_family] at hc
  obtain ⟨H, hp⟩ := pinchedSliceHomotopyFamily_exists_of_comp f (𝟙 K) c (by
    rw [hf, Category.id_comp]
    exact hc.symm)
  refine ⟨(β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h, ?_, ?_, ?_⟩
  · change SSet.ι₀ ≫ H.h = _
    exact H.h₀
  · change SSet.ι₁ ≫ H.h = _
    simpa only [Category.id_comp] using H.h₁
  · have hf' : f ≫ pinchedHomToIntervalMappingSpace x y =
        SSet.const (intervalMappingVertexOfEdge (SSet.Edge.ofTruncated (X := X) e)) := by
      simp only [f, SSet.const_comp, pinchedHomToIntervalMappingSpace_vertex,
        s, Equiv.apply_symm_apply]
      rfl
    rw [Category.assoc, hp, hf', intervalFamilyHomotopy_const_edge_h,
      ← Category.assoc, braiding_hom_snd]
    rfl

end SerrePositivity.InfinityCategories

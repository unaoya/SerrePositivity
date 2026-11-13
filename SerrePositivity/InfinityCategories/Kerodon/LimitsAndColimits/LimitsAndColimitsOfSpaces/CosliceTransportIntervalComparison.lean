module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CosliceEdgeTriangleFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence

/-!
概要：元の coslice 輸送と、同じ区間比較による標準後合成との全族比較。
方針：選ばれた輸送の同じ証人を実三角形へ読み、区間族の忠実性を使う。
規約：輸送や区間比較を選び直さない。使われ方：表現可能値の比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：区間の始点の面は、元の prism の零端点を定値に引き戻した射。
方針：一点からの Yoneda 射の同定を使う。
規約：パラメータは任意。使われ方：元の輸送証人の第一面。 -/
lemma intervalFace_first_prismEndpoint (A : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 2) ▷ A) = snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 0 A := by
  have he : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [he]
  rfl

/-- 概要：区間の終点の面は、元の prism の一端点を定値に引き戻した射。
方針：一点からの Yoneda 射の同定を使う。
規約：パラメータは任意。使われ方：元の輸送証人の長辺。 -/
lemma intervalFace_last_prismEndpoint (A : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 2) ▷ A) = snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 1 A := by
  have he : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [he]
  rfl

/-- 概要：同じ coslice の標準輸送の区間像は、元の比較族の標準後合成にホモトピック。
方針：同じ輸送証人の実三角形の三面から合成則を得る。
規約：全 fiber をパラメータにする。使われ方：表現可能値の射の自然性。 -/
lemma cosliceTransport_interval_homotopy {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {c d : X _⦋0⦌} (e : X.Edge c d) :
    Nonempty (SSet.Homotopy
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
        cosliceFiberToIntervalMappingSpace x d)
      (cosliceFiberToIntervalMappingSpace x c ≫ intervalPostcompose x
        (SSet.Truncated.HomotopyCategory.homMk e))) := by
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let A := vertexFiber q c
  let β := edgeTransport q e
  obtain ⟨H, h₀, h₁, hp, _⟩ := edgeTransport_isTransport q e
  have f₀ : (stdSimplex.δ (1 : Fin 2) ▷ A) ≫ H =
      snd (Δ[0] : SSet.{u}) A ≫ (𝟙 A) ≫ vertexFiberι q c := by
    rw [intervalFace_first_prismEndpoint, Category.assoc, h₀, Category.id_comp]
  have f₁ : (stdSimplex.δ (0 : Fin 2) ▷ A) ≫ H =
      snd (Δ[0] : SSet.{u}) A ≫ β ≫ vertexFiberι q d := by
    rw [intervalFace_last_prismEndpoint, Category.assoc, h₁]
  have hfirst := cosliceEdgeTriangleFamily_side x c H (1 : Fin 2) (𝟙 A) f₀
  have hlast := cosliceEdgeTriangleFamily_side x d H (0 : Fin 2) β f₁
  have hsecond : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ cosliceEdgeTriangleFamily x H =
      (intervalFamilyHomotopy (SSet.const (intervalMappingVertexOfEdge e) : A ⟶ _)).h := by
    rw [cosliceEdgeTriangleFamily_edge, hp, intervalFamilyHomotopy_const_edge]
    rfl
  simp only [Fin.succ, Category.id_comp] at hfirst hlast
  have hcomp := intervalTriangleFamily_hom_comp
    (cosliceFiberToIntervalMappingSpace x c)
    (SSet.const (intervalMappingVertexOfEdge e) : A ⟶ _)
    (β ≫ cosliceFiberToIntervalMappingSpace x d)
    (cosliceEdgeTriangleFamily x H) hfirst hsecond hlast
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, ← hcomp, intervalFamilyHom_const_edge]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

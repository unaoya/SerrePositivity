module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：単体的区間の境界と二つの端点の余積の同定。
方針：境界の単体は頂点値零を欠くか一を欠くので定数単体である。
規約：第一成分が終点、第二成分が始点。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。円からの Hom と path fiber の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：区間の二つの頂点を境界内の頂点として表す。
方針：一つの頂点の像は両頂点へ全射でないことを使う。
規約：i は Fin 2。
使われ方：Goerss–Jardine I §7。境界への端点射。 -/
def intervalBoundaryVertex (i : Fin 2) : (∂Δ[1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm i, by
    change ¬Function.Surjective (stdSimplex.asOrderHom (stdSimplex.obj₀Equiv.symm i))
    intro h
    fin_cases i
    · obtain ⟨j, hj⟩ := h 1
      change (0 : Fin 2) = 1 at hj
      contradiction
    · obtain ⟨j, hj⟩ := h 0
      change (1 : Fin 2) = 0 at hj
      contradiction⟩

/-- 概要：二つの端点の余積から区間の境界への射。
方針：終点と始点への定数射を余積の普遍性で貼る。
規約：余積の順は終点・始点。
使われ方：Goerss–Jardine I §7。境界の具体的な分解。 -/
def intervalBoundaryMap : (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ⟶ (∂Δ[1] : SSet.{u}) :=
  coprod.desc (SSet.const (intervalBoundaryVertex 1)) (SSet.const (intervalBoundaryVertex 0))

/-- 概要：境界への端点射を区間へ含めると終点包含の基礎射になる。
方針：余積の両成分で定数射を計算する。
規約：基点成分も含む。
使われ方：Goerss–Jardine I §7。円の商の比較。 -/
@[reassoc (attr := simp)]
theorem intervalBoundaryMap_ι : intervalBoundaryMap.{u} ≫ (boundary 1).ι =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right := by
  apply coprod.hom_ext <;>
    simp [intervalBoundaryMap, intervalBoundaryVertex]

/-- 概要：境界への端点射は単射。
方針：区間への合成が単射であることを使う。
規約：単体集合の単射。
使われ方：Kerodon §3.1.3（Tag 00TJ）。境界との同型。 -/
instance intervalBoundaryMap_mono : Mono intervalBoundaryMap.{u} := by
  have : Mono (intervalBoundaryMap.{u} ≫ (boundary 1).ι) := by
    rw [intervalBoundaryMap_ι]
    infer_instance
  exact mono_of_mono (intervalBoundaryMap.{u}) (boundary 1).ι

/-- 概要：境界内の任意の単体は端点のいずれかの像。
方針：欠けている頂点を選び、残る頂点で定数であることを示す。
規約：全単体次数での全射性。
使われ方：Goerss–Jardine I §7。境界と端点余積の同型。 -/
theorem intervalBoundaryMap_surjective (m : SimplexCategoryᵒᵖ) :
    Function.Surjective (intervalBoundaryMap.{u}.app m) := by
  intro s
  have hs : ¬Function.Surjective (stdSimplex.asOrderHom s.val) := s.property
  simp only [Function.Surjective, not_forall, not_exists] at hs
  obtain ⟨v, hv⟩ := hs
  fin_cases v
  · refine ⟨(coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m PUnit.unit, ?_⟩
    apply Subtype.ext
    change ((coprod.inl ≫ intervalBoundaryMap.{u} ≫ (boundary 1).ι).app m PUnit.unit) = s.val
    rw [intervalBoundaryMap_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]
    apply stdSimplex.ext
    intro j
    change (1 : Fin 2) = (stdSimplex.asOrderHom s.val) j
    have hh := hv j
    apply Fin.ext
    have ht := ((stdSimplex.asOrderHom s.val) j).isLt
    have hn : ((stdSimplex.asOrderHom s.val) j).val ≠ 0 := fun h ↦ hh (Fin.ext h)
    omega
  · refine ⟨(coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})).app m PUnit.unit, ?_⟩
    apply Subtype.ext
    change ((coprod.inr ≫ intervalBoundaryMap.{u} ≫ (boundary 1).ι).app m PUnit.unit) = s.val
    rw [intervalBoundaryMap_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr]
    apply stdSimplex.ext
    intro j
    change (0 : Fin 2) = (stdSimplex.asOrderHom s.val) j
    have hh := hv j
    apply Fin.ext
    have ht := ((stdSimplex.asOrderHom s.val) j).isLt
    have hn : ((stdSimplex.asOrderHom s.val) j).val ≠ 1 := fun h ↦ hh (Fin.ext h)
    omega

/-- 概要：区間の境界は二つの端点の余積と同型。
方針：全次数での単射性と全射性を使う。
規約：選んだ端点射自身が同型となる。
使われ方：Goerss–Jardine I §7。円の商と path fiber の比較。 -/
instance intervalBoundaryMap_isIso : IsIso intervalBoundaryMap.{u} := by
  have : ∀ m, IsIso (intervalBoundaryMap.{u}.app m) := fun m ↦
    (CategoryTheory.isIso_iff_bijective _).2
      ⟨(mono_iff_injective _).1 inferInstance, intervalBoundaryMap_surjective m⟩
  exact NatIso.isIso_of_isIso_app intervalBoundaryMap

end

end SerrePositivity.KST.Spectra

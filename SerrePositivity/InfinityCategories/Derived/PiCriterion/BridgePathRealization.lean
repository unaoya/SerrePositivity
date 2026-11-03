module

public import SerrePositivity.InfinityCategories.Derived.PiCriterion.BridgePathTranspose
public import SerrePositivity.InfinityCategories.Derived.PiCriterion.PathFamilyHomotopy

/-!
概要：指定辺を表す path 頂点の群の類から、D の指定辺付き球面円柱を実現する。
方針：代表単体の path の族を uncurry し、境界の定数 path 族を同じ指定辺へ戻す。
規約：D の移送条件と固定した path 頂点の群の表示を双方向に接続する。
使われ方：D の正次数の元ごとの条件を実際の群の全単射性へ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra
variable {X : SSet.{u}}

/-- 指定辺を表す定数 path の族を円柱に戻すと、その同じ辺をたどる。 -/
lemma pathFamilyHomotopy_constant_edge {x y : X _⦋0⦌} (e : X.Edge x y) (K : SSet.{u}) :
    (pathFamilyHomotopy (SSet.const (edgePathVertex e) : K ⟶ _)).h =
      snd K (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge := by
  change (β_ K (Δ[1] : SSet.{u})).hom ≫
    uncurry (SSet.const (edgePathVertex e) : K ⟶ _) = _
  rw [← edgePathUnit_constant e K, uncurry_natural_left, edgePathUnit, uncurry_curry]
  simp only [← Category.assoc, whiskerLeft_fst, braiding_hom_fst]

/-- 固定した指定辺の path 頂点における一つの群の類を、D の球面円柱で実現する。 -/
lemma bridge_transport_path_realization [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y)
    (h₀ : (KanPath.evaluation X 0).app _ (edgePathVertex e) = x)
    (h₁ : (KanPath.evaluation X 1).app _ (edgePathVertex e) = y)
    (γ : KanHomotopyGroup (KanPath.object X) n (edgePathVertex e)) :
    dgBarCompactPiTransport n e
      (KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ γ)
      (KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ γ) := by
  obtain ⟨t, rfl⟩ := Quotient.mk_surjective γ
  let f := mapSimplex (KanPath.evaluation X 0) h₀ t
  let g := mapSimplex (KanPath.evaluation X 1) h₁ t
  let H : SSet.Homotopy f.map g.map := pathFamilyHomotopy t.map
  refine ⟨f, g, rfl, rfl, H, ?_⟩
  change (boundary (n + 1)).ι ▷ (Δ[1] : SSet.{u}) ≫ (pathFamilyHomotopy t.map).h = _
  rw [pathFamilyHomotopy_precomp, t.comm, Subcomplex.ofSimplex_ι, SSet.comp_const]
  exact pathFamilyHomotopy_constant_edge e _

/-- D の指定辺付き移送は、その同じ辺の固定 path 頂点の群の表示と同値。 -/
lemma bridge_transport_iff_path_witness [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y) (a : KanHomotopyGroup X n x) (b : KanHomotopyGroup X n y) :
    dgBarCompactPiTransport n e a b ↔
      ∃ h₀ : (KanPath.evaluation X 0).app _ (edgePathVertex e) = x,
      ∃ h₁ : (KanPath.evaluation X 1).app _ (edgePathVertex e) = y,
      ∃ γ : KanHomotopyGroup (KanPath.object X) n (edgePathVertex e),
        KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ γ = a ∧
        KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ γ = b := by
  constructor
  · exact bridge_transport_path_witness n e a b
  · rintro ⟨h₀, h₁, γ, ha, hb⟩
    have h := bridge_transport_path_realization n e h₀ h₁ γ
    simpa only [ha, hb] using h

/-- 指定辺を表す path 頂点の零端点は、元の辺の始点そのもの。 -/
lemma edgePathVertex_zero {x y : X _⦋0⦌} (e : X.Edge x y) :
    (KanPath.evaluation X 0).app _ (edgePathVertex e) = x := by
  let r : (Δ[0] : SSet.{u}) ⟶ KanPath.object X := SSet.const (edgePathVertex e)
  have hh := (pathFamilyHomotopy r).h₀
  change SSet.ι₀ ≫ (pathFamilyHomotopy r).h = r ≫ KanPath.evaluation X 0 at hh
  rw [pathFamilyHomotopy_constant_edge] at hh
  have hi : (SSet.ι₀ : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⊗ Δ[1]) ≫ snd _ _ =
      stdSimplex.δ (1 : Fin 2) := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  rw [← Category.assoc, hi, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq,
    SSet.yonedaEquiv_symm_zero, SSet.const_comp] at hh
  have hv := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) hh
  simpa [SSet.const] using hv.symm

/-- 指定辺を表す path 頂点の一端点は、元の辺の終点そのもの。 -/
lemma edgePathVertex_one {x y : X _⦋0⦌} (e : X.Edge x y) :
    (KanPath.evaluation X 1).app _ (edgePathVertex e) = y := by
  let r : (Δ[0] : SSet.{u}) ⟶ KanPath.object X := SSet.const (edgePathVertex e)
  have hh := (pathFamilyHomotopy r).h₁
  change SSet.ι₁ ≫ (pathFamilyHomotopy r).h = r ≫ KanPath.evaluation X 1 at hh
  rw [pathFamilyHomotopy_constant_edge] at hh
  have hi : (SSet.ι₁ : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⊗ Δ[1]) ≫ snd _ _ =
      stdSimplex.δ (0 : Fin 2) := by
    rw [stdSimplex.δ_zero_eq_const]
    rfl
  rw [← Category.assoc, hi, stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq,
    SSet.yonedaEquiv_symm_zero, SSet.const_comp] at hh
  have hv := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) hh
  simpa [SSet.const] using hv.symm

/-- D の指定辺に沿う基点移送を、実際の正次数の群同型として表す。 -/
def bridgePiTransportEquiv [KanComplex X] (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y) :
    KanHomotopyGroup X n x ≃* KanHomotopyGroup X n y :=
  (KanHomotopyGroup.equivOfPiIsomorphism n (KanPath.evaluation X 0)
    (KanPath.evaluation_piIsomorphism X 0) (edgePathVertex_zero e)).symm.trans
  (KanHomotopyGroup.equivOfPiIsomorphism n (KanPath.evaluation X 1)
    (KanPath.evaluation_piIsomorphism X 1) (edgePathVertex_one e))

/-- D の球面円柱の関係は、同じ指定辺による群同型の値の等式に一致。 -/
lemma bridge_transport_iff_equiv [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y) (a : KanHomotopyGroup X n x) (b : KanHomotopyGroup X n y) :
    dgBarCompactPiTransport n e a b ↔ bridgePiTransportEquiv n e a = b := by
  let E₀ := KanHomotopyGroup.equivOfPiIsomorphism n (KanPath.evaluation X 0)
    (KanPath.evaluation_piIsomorphism X 0) (edgePathVertex_zero e)
  let E₁ := KanHomotopyGroup.equivOfPiIsomorphism n (KanPath.evaluation X 1)
    (KanPath.evaluation_piIsomorphism X 1) (edgePathVertex_one e)
  change dgBarCompactPiTransport n e a b ↔ E₁ (E₀.symm a) = b
  constructor
  · intro h
    obtain ⟨h₀, h₁, γ, ha, hb⟩ := bridge_transport_path_witness n e a b h
    have hzero : E₀ γ = a := by
      simpa only [E₀, KanHomotopyGroup.equivOfPiIsomorphism_apply] using ha
    have hone : E₁ γ = b := by
      simpa only [E₁, KanHomotopyGroup.equivOfPiIsomorphism_apply] using hb
    rw [← hzero, E₀.symm_apply_apply, hone]
  · intro h
    have ha : KanHomotopyGroup.map (KanPath.evaluation X 0) (edgePathVertex_zero e)
        (E₀.symm a) = a := by
      simpa only [E₀, KanHomotopyGroup.equivOfPiIsomorphism_apply] using E₀.apply_symm_apply a
    have hb : KanHomotopyGroup.map (KanPath.evaluation X 1) (edgePathVertex_one e)
        (E₀.symm a) = b := by
      simpa only [E₁, KanHomotopyGroup.equivOfPiIsomorphism_apply] using h
    have ht := bridge_transport_path_realization n e (edgePathVertex_zero e)
      (edgePathVertex_one e) (E₀.symm a)
    simpa only [ha, hb] using ht

end SerrePositivity.InfinityCategories.F2.PiCriterion

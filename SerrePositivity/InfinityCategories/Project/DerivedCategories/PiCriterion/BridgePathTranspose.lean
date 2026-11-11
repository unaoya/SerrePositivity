module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.SphereClassPath
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：D が指定する実際の辺を、指数 path 対象の固定した基点として保持する。
方針：指定辺の定数パラメータ族を curry し、球面円柱の境界式を転置する。
規約：移送の辺を選び直さず、D の dgBarCompactPiTransport を直接消費する。
使われ方：指定辺に沿う π 移送の一意性と、全空間比較の群の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {X : SSet.{u}}

/-- 指定された実際の辺を、単位をパラメータとする path 族として読む。 -/
def edgePathUnit {x y : X _⦋0⦌} (e : X.Edge x y) :
    (𝟙_ SSet.{u}) ⟶ KanPath.object X :=
  curry (fst (Δ[1] : SSet.{u}) (𝟙_ SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge)

/-- 指定辺そのものを表す指数 path 対象の頂点。 -/
def edgePathVertex {x y : X _⦋0⦌} (e : X.Edge x y) : (KanPath.object X) _⦋0⦌ :=
  SSet.unitHomEquiv _ (edgePathUnit e)

/-- 定数な path の族は同じ指定辺の単位族を前合成したもの。 -/
lemma edgePathUnit_constant {x y : X _⦋0⦌} (e : X.Edge x y) (K : SSet.{u}) :
    toUnit K ≫ edgePathUnit e = (SSet.const (edgePathVertex e) : K ⟶ _) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (Under.mk (edgePathUnit e)) K

/-- D の指定辺をたどる球面円柱の転置は、境界上でその同じ path 頂点に定数。 -/
lemma bridge_transport_transpose_boundary {x y : X _⦋0⦌}
    (e : X.Edge x y) (n : ℕ)
    (f : X.PtSimplex (n + 1) x) (g : X.PtSimplex (n + 1) y)
    (H : SSet.Homotopy f.map g.map)
    (hH : (boundary (n + 1)).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      snd _ _ ≫ SSet.yonedaEquiv.symm e.edge) :
    (boundary (n + 1)).ι ≫ KanPath.transpose H = SSet.const (edgePathVertex e) := by
  rw [← edgePathUnit_constant e (boundary (n + 1) : SSet.{u})]
  apply uncurry_injective
  rw [uncurry_natural_left, KanPath.transpose, uncurry_curry,
    uncurry_natural_left, edgePathUnit, uncurry_curry]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc, hH,
    ← Category.assoc, braiding_hom_snd, ← Category.assoc, whiskerLeft_fst]

/-- D の基点移送は、指定辺を表す固定した path 頂点における一つの群の類から来る。 -/
lemma bridge_transport_path_witness [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b) :
    ∃ h₀ : (KanPath.evaluation X 0).app _ (edgePathVertex e) = x,
      ∃ h₁ : (KanPath.evaluation X 1).app _ (edgePathVertex e) = y,
      ∃ γ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n (edgePathVertex e),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ γ = a ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ γ = b := by
  obtain ⟨f, g, hf, hg, H, hH⟩ := h
  let t : (KanPath.object X).PtSimplex (n + 1) (edgePathVertex e) :=
    { map := KanPath.transpose H
      comm := by
        rw [Subcomplex.ofSimplex_ι, SSet.comp_const]
        exact bridge_transport_transpose_boundary e n f g H hH }
  have hm₀ : t.map ≫ KanPath.evaluation X 0 = f.map := KanPath.transpose_zero H
  have hm₁ : t.map ≫ KanPath.evaluation X 1 = g.map := KanPath.transpose_one H
  have h₀ : (KanPath.evaluation X 0).app _ (edgePathVertex e) = x := by
    have hh := congrArg (fun k ↦ k ≫ KanPath.evaluation X 0) (t.δ_map 0)
    simp only [Category.assoc, hm₀, f.δ_map, SSet.const_comp] at hh
    have hv := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) hh
    simpa [SSet.const] using hv.symm
  have h₁ : (KanPath.evaluation X 1).app _ (edgePathVertex e) = y := by
    have hh := congrArg (fun k ↦ k ≫ KanPath.evaluation X 1) (t.δ_map 0)
    simp only [Category.assoc, hm₁, g.δ_map, SSet.const_comp] at hh
    have hv := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))) hh
    simpa [SSet.const] using hv.symm
  refine ⟨h₀, h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t, ?_, ?_⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (KanPath.evaluation X 0) h₀ t = f := RelativeMorphism.ext hm₀
    rw [ht, hf]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (KanPath.evaluation X 1) h₁ t = g := RelativeMorphism.ext hm₁
    rw [ht, hg]

/-- 指定した同じ辺に沿う D の基点移送は、始点の類から終点の類を一意に定める。 -/
lemma bridge_transport_right_unique [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y) {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b) (h' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a c) : b = c := by
  obtain ⟨h₀, h₁, γ, ha, hb⟩ := bridge_transport_path_witness n e a b h
  obtain ⟨h₀', h₁', γ', ha', hc⟩ := bridge_transport_path_witness n e a c h'
  have he : γ = γ' :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation X 0)
      (KanPath.evaluation_piIsomorphism X 0) h₀).injective (ha.trans ha'.symm)
  exact hb.symm.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁) he).trans hc)

/-- 指定した同じ辺に沿う D の基点移送は、終点の類から始点の類も一意に定める。 -/
lemma bridge_transport_left_unique [KanComplex X] (n : ℕ) {x y : X _⦋0⦌}
    (e : X.Edge x y) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a c) (h' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e b c) : a = b := by
  obtain ⟨h₀, h₁, γ, ha, hc⟩ := bridge_transport_path_witness n e a c h
  obtain ⟨h₀', h₁', γ', hb, hc'⟩ := bridge_transport_path_witness n e b c h'
  have he : γ = γ' :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation X 1)
      (KanPath.evaluation_piIsomorphism X 1) h₁).injective (hc.trans hc'.symm)
  exact ha.symm.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀) he).trans hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgePathRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelation

/-!
概要：指数 path の任意の頂点を、両端を保つ元の実際の辺として読み戻す。
方針：単位対象からの射の curry を解き、辺の path 頂点との往復を計算する。
規約：D の指定辺の条件は、選んだ同じ辺に対して適用する。
使われ方：群の実際の path 上の比較から、D が量化する辺を選ぶ。
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

/-- path 頂点の単位族を uncurry して得る、元の区間からの射。 -/
def pathVertexMap (z : (KanPath.object X) _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ X :=
  (ρ_ (Δ[1] : SSet.{u})).inv ≫ uncurry ((SSet.unitHomEquiv _).symm z)

/-- まず両端を面として保持した、元の path 頂点の辺。 -/
def pathVertexRawEdge (z : (KanPath.object X) _⦋0⦌) :
    X.Edge (X.δ 1 (SSet.yonedaEquiv (pathVertexMap z)))
      (X.δ 0 (SSet.yonedaEquiv (pathVertexMap z))) where
  edge := SSet.yonedaEquiv (pathVertexMap z)
  src_eq := rfl
  tgt_eq := rfl

lemma pathVertexRawEdge_path (z : (KanPath.object X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex (pathVertexRawEdge z) = z := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathUnit (pathVertexRawEdge z) = (SSet.unitHomEquiv _).symm z := by
    change curry (fst (Δ[1] : SSet.{u}) (𝟙_ SSet.{u}) ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (pathVertexMap z))) = _
    rw [Equiv.symm_apply_apply]
    have hf : fst (Δ[1] : SSet.{u}) (𝟙_ SSet.{u}) = (ρ_ (Δ[1] : SSet.{u})).hom := rfl
    rw [hf, pathVertexMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, curry_uncurry]
  exact (congrArg (SSet.unitHomEquiv _) h).trans ((SSet.unitHomEquiv _).apply_symm_apply z)

/-- 任意の path 頂点は、指定した同じ両端を持つ実際の辺から来る。 -/
lemma pathVertexEdge_exists (z : (KanPath.object X) _⦋0⦌) {x y : X _⦋0⦌}
    (h₀ : (KanPath.evaluation X 0).app _ z = x)
    (h₁ : (KanPath.evaluation X 1).app _ z = y) :
    ∃ e : X.Edge x y, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex e = z := by
  let e := pathVertexRawEdge z
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex e = z := pathVertexRawEdge_path z
  have hx : X.δ 1 e.edge = x := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex_zero e
    rw [he] at h
    exact h.symm.trans h₀
  have hy : X.δ 0 e.edge = y := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex_one e
    rw [he] at h
    exact h.symm.trans h₁
  exact ⟨e.ofEq hx hy, he⟩

/-- 実際の path による二類の比較は、ある同じ辺をたどる D の円柱として実現できる。 -/
lemma piPathRelated_iff_exists_transport [KanComplex X] (n : ℕ)
    {x y : X _⦋0⦌} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelated n a b ↔ ∃ e : X.Edge x y, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b := by
  constructor
  · rintro ⟨z, h₀, h₁, γ, ha, hb⟩
    obtain ⟨e, he⟩ := pathVertexEdge_exists z h₀ h₁
    subst z
    refine ⟨e, ?_⟩
    simpa only [ha, hb] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_transport_path_realization n e h₀ h₁ γ
  · rintro ⟨e, h⟩
    obtain ⟨h₀, h₁, γ, ha, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_transport_path_witness n e a b h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.edgePathVertex e, h₀, h₁, γ, ha, hb⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

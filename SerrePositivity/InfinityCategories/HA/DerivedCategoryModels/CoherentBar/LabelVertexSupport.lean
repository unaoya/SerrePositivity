module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalizationRecurrence
public import Mathlib.LinearAlgebra.Finsupp.Supported
/-!
概要：Mathlib のラベル正規化は元の単体の始点ごとの支持を保つ。
方針：始点を保つ面と退化の自由加群写像を、既存の P の再帰式へ渡す。
規約：ラベル複体上の結果。実 bar の高次 prefix 項の比較は別に証明する。
使われ方：同じ始点の実加群への正規化係数の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R] (I : SSet.{u})

def dgCoherentBarLabelFirstVertex {n : ℕ} (s : I _⦋n⦌) : I _⦋0⦌ :=
  I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s

lemma dgCoherentBarLabelFirstVertex_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    dgCoherentBarLabelFirstVertex I (I.map f.op s) = dgCoherentBarLabelFirstVertex I s := by
  have hc : SimplexCategory.const ⦋0⦌ ⦋m⦌ 0 ≫ f =
      SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 := by
    rw [SimplexCategory.const_comp, hf]
  exact (ConcreteCategory.congr_hom
    (I.map_comp f.op (SimplexCategory.const ⦋0⦌ ⦋m⦌ 0).op) s).symm.trans
      (by rw [← op_comp, hc])

def dgCoherentBarLabelVertexSupport (n : ℕ) (v : I _⦋0⦌) :
    Submodule R (I _⦋n⦌ →₀ R) :=
  Finsupp.supported R R {s | dgCoherentBarLabelFirstVertex I s = v}

lemma dgCoherentBarLabelVertexSupport_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (v : I _⦋0⦌) (z : I _⦋n⦌ →₀ R)
    (hz : z ∈ dgCoherentBarLabelVertexSupport R I n v) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I).map f.op z ∈
      dgCoherentBarLabelVertexSupport R I m v := by
  apply Finsupp.supported_comap_lmapDomain R R (I.map f.op)
    {s | dgCoherentBarLabelFirstVertex I s = v}
  change z ∈ Finsupp.supported R R
    {s | dgCoherentBarLabelFirstVertex I (I.map f.op s) = v}
  simpa only [dgCoherentBarLabelFirstVertex_map I f hf, dgCoherentBarLabelVertexSupport] using hz

lemma dgCoherentBarLabelStage_preserves_vertex_support (q n : ℕ) (v : I _⦋0⦌)
    (z : I _⦋n⦌ →₀ R) (hz : z ∈ dgCoherentBarLabelVertexSupport R I n v) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage R I q).f n z ∈ dgCoherentBarLabelVertexSupport R I n v := by
  induction q with
  | zero => exact hz
  | succ q ih =>
    cases n with
    | zero => simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage_zero_f, ModuleCat.id_apply] using hz
    | succ n =>
      by_cases hn : n < q
      · rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage_stable_f R I hn]
        exact ih
      · obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
        erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage_succ_f R I (q := q) (a := a) (by omega)]
        let zq : I _⦋n + 1⦌ →₀ R := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage R I q).f (n + 1) z
        let zd : I _⦋n⦌ →₀ R := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I).δ ⟨a + 1, by omega⟩ zq
        let zs : I _⦋n + 1⦌ →₀ R := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I).σ ⟨a, by omega⟩ zd
        change zq - zs ∈ dgCoherentBarLabelVertexSupport R I (n + 1) v
        apply Submodule.sub_mem _ ih
        apply dgCoherentBarLabelVertexSupport_map R I (SimplexCategory.σ ⟨a, by omega⟩)
          (by simp [SimplexCategory.σ, Fin.predAboveOrderHom]) v
        apply dgCoherentBarLabelVertexSupport_map R I (SimplexCategory.δ ⟨a + 1, by omega⟩)
          (by simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]) v
        exact ih

lemma dgCoherentBarLabelProjection_preserves_vertex_support (n : ℕ) (v : I _⦋0⦌)
    (z : I _⦋n⦌ →₀ R) (hz : z ∈ dgCoherentBarLabelVertexSupport R I n v) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection R I).f n z ∈ dgCoherentBarLabelVertexSupport R I n v := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection, PInfty_f]
  exact dgCoherentBarLabelStage_preserves_vertex_support R I n n v z hz

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

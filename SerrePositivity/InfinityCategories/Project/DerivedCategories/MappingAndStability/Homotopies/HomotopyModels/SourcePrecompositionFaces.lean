module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SourcePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornComponents

/-! # 始点への前合成と面への制限

概要：前合成した単体の始点を落とすと元の面になり、始点を保つ単射への制限は前合成と可換。
方針：射族の各成分に単射引き戻しの公式を適用する。
規約：dg 圏の全次数。使われ方：D7 の比較三単体の面。
-/
@[expose] public section
noncomputable section
open CategoryTheory SerrePositivity.DifferentialGraded

set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {n : ℕ} (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D (n + 1)) {Y : D}
  (g : zeroCycles (homObject R D Y (σ.obj 0)))
/-- 始点を落とす面は元の単体の同じ面。 -/
lemma simplex_pullback_succ :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
    σ.pullback (Fin.succOrderEmb (n + 1)).toOrderHom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (s := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g).pullback
    (Fin.succOrderEmb (n + 1)).toOrderHom).toSimplexData)
    (t := (σ.pullback (Fin.succOrderEmb (n + 1)).toOrderHom).toSimplexData) rfl ?_
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise rfl
  intro I a b k hI ha hb hk
  apply heq_of_eq
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.data σ.toSimplexData g).hom
        (I.image (Fin.succOrderEmb (n + 1)).toOrderHom) a.succ b.succ k _ _ _ _ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
        (Fin.succOrderEmb (n + 1)).injective.injOn
    _ = σ.hom (I.image (Fin.succOrderEmb (n + 1)).toOrderHom)
        a.succ b.succ k _ _ _ _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_succ σ.toSimplexData g _ _ _ _ _ _ _ _
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj σ.toSimplexData
      (Fin.succOrderEmb (n + 1)).toOrderHom I a b k hI ha hb hk
      (Fin.succOrderEmb (n + 1)).injective.injOn).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {m n : ℕ}
/-- 単調写像の前に新しい零頂点を付ける。 -/
def extend (θ : Fin m →o Fin n) : Fin (m + 1) →o Fin (n + 1) where
  toFun := Fin.cases 0 (fun i => (θ i).succ)
  monotone' := by
    intro a b hab
    cases a using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ a =>
      cases b using Fin.cases with
      | zero => simp at hab
      | succ b => exact Fin.succ_le_succ_iff.mpr (θ.monotone (Fin.succ_le_succ_iff.mp hab))
/-- 零頂点を付ける操作は単射性を保つ。 -/
lemma extend_injective (θ : Fin m →o Fin n) (hθ : Function.Injective θ) :
    Function.Injective (extend θ) := by
  intro a b hab
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => rfl
    | succ b => exact False.elim (Fin.succ_ne_zero _ hab.symm)
  | succ a =>
    cases b using Fin.cases with
    | zero => exact False.elim (Fin.succ_ne_zero _ hab)
    | succ b => exact congrArg Fin.succ (hθ (Fin.succ_injective _ hab))
variable {Y : D}
/-- 始点を保つ単射での引き戻しは始点への前合成と可換。 -/
lemma simplex_pullback_extend (θ : Fin m →o Fin n) (hθ : Function.Injective θ)
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (g : zeroCycles (homObject R D Y (σ.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g).pullback (extend θ) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (σ.pullback (extend θ)) g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  have hobj : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g).pullback (extend θ)).obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (σ.pullback (extend θ)) g).obj := by
    funext i
    cases i using Fin.cases <;> rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  have hab : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card hI
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => simp at hab
    | succ b =>
      apply heq_of_eq
      change _ = compose R ((σ.toSimplexData.pullback (extend θ)).hom I 0 b.succ k
        hI ha hb hk) g.val (zero_add k)
      calc
        _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.data σ.toSimplexData g).hom (I.image (extend θ))
            0 (θ b).succ k _ _ _ _ :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
            (extend_injective θ hθ).injOn
        _ = compose R (σ.hom (I.image (extend θ)) 0 (θ b).succ k _ _ _ _) g.val
            (zero_add k) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_zero _ _ _ _ _ _ _ _ _
        _ = _ := congrArg (fun z => compose R z g.val (zero_add k))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj σ.toSimplexData (extend θ) I 0 b.succ k hI ha hb hk
            (extend_injective θ hθ).injOn).symm
  | succ a =>
    cases b using Fin.cases with
    | zero => simp at hab
    | succ b =>
      apply heq_of_eq
      change _ = (σ.toSimplexData.pullback (extend θ)).hom I a.succ b.succ k hI ha hb hk
      calc
        _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.data σ.toSimplexData g).hom (I.image (extend θ))
            (θ a).succ (θ b).succ k _ _ _ _ :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
            (extend_injective θ hθ).injOn
        _ = σ.hom (I.image (extend θ)) (θ a).succ (θ b).succ k _ _ _ _ :=
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.hom_succ _ _ _ _ _ _ _ _ _ _
        _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj σ.toSimplexData (extend θ)
            I a.succ b.succ k hI ha hb hk
            (extend_injective θ hθ).injOn).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {n : ℕ} (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) {Y : D}
  (g : zeroCycles (homObject R D Y (σ.obj 0)))
/-- 始点を複製した退化単体に前合成して比較単体を作る。 -/
def prepend : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom) g
/-- 比較単体の零面は元の単体。 -/
lemma prepend_face_zero :
    (prepend σ g).pullback (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = σ := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom) g).pullback
    (Fin.succOrderEmb (n + 1)).toOrderHom = σ
  rw [simplex_pullback_succ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
  change σ.pullback (SimplexCategory.δ (0 : Fin (n + 2)) ≫
    SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom = σ
  exact (congrArg (fun θ : SimplexCategory.mk n ⟶ SimplexCategory.mk n =>
    σ.pullback θ.toOrderHom) (SimplexCategory.δ_comp_σ_self (i := (0 : Fin (n + 1))))).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id σ)
/-- 単体と閉零射の等式に沿って前合成単体を比較する。 -/
lemma simplex_congr {σ τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n} (h : σ = τ)
    {g : zeroCycles (homObject R D Y (σ.obj 0))}
    {g' : zeroCycles (homObject R D Y (τ.obj 0))} (hg : HEq g g') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex τ g' := by
  cases h
  cases hg
  rfl
/-- 比較単体の一面は元の単体の始点への前合成。 -/
lemma prepend_face_one :
    (prepend σ g).pullback (SimplexCategory.δ (1 : Fin (n + 2))).toOrderHom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex σ g := by
  have h : (σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom).pullback
      (SimplexCategory.δ (1 : Fin (n + 2))).toOrderHom = σ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
    exact (congrArg (fun θ : SimplexCategory.mk n ⟶ SimplexCategory.mk n =>
      σ.pullback θ.toOrderHom) (SimplexCategory.δ_comp_σ_succ (i := (0 : Fin (n + 1))))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id σ)
  have he : (SimplexCategory.δ (1 : Fin (n + 2))).toOrderHom =
      extend (Fin.succOrderEmb n).toOrderHom := by
    ext i
    cases i using Fin.cases <;> simp [SimplexCategory.δ, extend]
  let τ := σ.pullback (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex τ g).pullback (extend (Fin.succOrderEmb n).toOrderHom) :=
      congrArg (fun θ => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex τ g).pullback θ) he
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (τ.pullback (extend (Fin.succOrderEmb n).toOrderHom)) g :=
      simplex_pullback_extend (Fin.succOrderEmb n).toOrderHom
        (Fin.succOrderEmb n).injective τ g
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex (τ.pullback (SimplexCategory.δ (1 : Fin (n + 2))).toOrderHom) g :=
      simplex_congr (congrArg (fun θ => τ.pullback θ) he.symm) (heq_of_eq rfl)
    _ = _ := simplex_congr h (heq_of_eq rfl)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

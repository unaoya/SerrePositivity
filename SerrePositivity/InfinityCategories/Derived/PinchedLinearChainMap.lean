module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearPullback

/-! # Hom 複体の鎖写像による pinched 線形成分の写像

概要：固定二対象の Hom 複体の鎖写像を全ての線形成分へ適用する。
方針：削除和との可換性と鎖写像の微分との可換性から方程式を保存する。
規約：対象写像は不要。使われ方：β3 の写像空間の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E] {x y : D} {x' y' : E}

/-- 鎖写像を線形データの各成分に適用する A 線形写像。 -/
def pinchedLinearDataMap (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ} :
    LinearData A x y n →ₗ[A] LinearData A x' y' n where
  toFun f i := φ.f i.val.2 (f i)
  map_add' f g := by funext i; exact (φ.f i.val.2).hom.map_add _ _
  map_smul' c f := by funext i; exact (φ.f i.val.2).hom.map_smul c (f i)

/-- 鎖写像による線形成分の写像は削除右辺と可換。 -/
lemma pinchedLinearDataMap_rhs (φ : homObject A D x y ⟶ homObject A E x' y')
    {n : ℕ} (f : LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    φ.f (k + 1) (f.rhs J k hk) = (pinchedLinearDataMap φ f).rhs J k hk := by
  unfold LinearData.rhs
  split_ifs
  · simp only [map_sum, Units.smul_def, map_zsmul, LinearData.component,
      pinchedLinearDataMap, LinearMap.coe_mk, AddHom.coe_mk]
  · exact map_zero _

/-- 方程式を満たす線形単体は鎖写像で再び線形単体になる。 -/
def pinchedLinearSimplexMap (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ} :
    LinearSimplex A x y n →ₗ[A] LinearSimplex A x' y' n where
  toFun s := ⟨pinchedLinearDataMap φ s.val, by
    intro J k hJ hk
    change (homObject A E x' y').d k (k + 1) (φ.f k (s.val.component J k hJ hk)) = _
    rw [← pinchedLinearDataMap_rhs]
    have h := ConcreteCategory.congr_hom (φ.comm k (k + 1)) (s.val.component J k hJ hk)
    change differential A (φ.f k (s.val.component J k hJ hk)) =
      φ.f (k + 1) (differential A (s.val.component J k hJ hk)) at h
    exact h.trans (congrArg (φ.f (k + 1)) (s.equation J k hJ hk))⟩
  map_add' s t := Subtype.ext (map_add (pinchedLinearDataMap φ) _ _)
  map_smul' c s := Subtype.ext (map_smul (pinchedLinearDataMap φ) c s.val)

/-- 成分への鎖写像の適用は任意の単調写像による引き戻しと可換。 -/
lemma pinchedLinearDataMap_pullback (φ : homObject A D x y ⟶ homObject A E x' y')
    {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (f : LinearData A x y n) :
    pinchedLinearDataMap φ (LinearData.pullback α f) =
      LinearData.pullback α (pinchedLinearDataMap φ f) := by
  funext i
  simp only [pinchedLinearDataMap, LinearData.pullback, LinearData.component,
    LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · rfl
  · exact map_zero _

/-- 線形単体への鎖写像の適用は面と退化を保存する。 -/
lemma pinchedLinearSimplexMap_pullback (φ : homObject A D x y ⟶ homObject A E x' y')
    {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (s : LinearSimplex A x y n) :
    pinchedLinearSimplexMap φ (LinearSimplex.pullback α s) =
      LinearSimplex.pullback α (pinchedLinearSimplexMap φ s) :=
  by
    apply Subtype.ext
    change pinchedLinearDataMap φ (LinearData.pullback α s.val) = _
    exact pinchedLinearDataMap_pullback φ α s.val

end SerrePositivity.InfinityCategories

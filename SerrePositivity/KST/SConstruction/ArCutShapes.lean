module
public import SerrePositivity.KST.SConstruction.ArCutSquare
public import SerrePositivity.KST.SConstruction.IdentityPushoutShapes

/-! # 切断四角形の三つの形状
概要：左側・切断点を跨ぐ区間・右側の切断四角形を計算する。
方針：切断端点を各領域で単純な区間写像に戻す。
規約：全単体での厳密な等号。使われ方：切断四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断点より左の端点の四角形は縦方向だけに変わる。 -/
lemma cutEndpoint_of_le {n : ℕ} (k i : Fin (n + 1)) (h : i ≤ k) (x y : Fin 2) :
    cutEndpoint k i x y = intervalStep i k h y := by
  fin_cases x <;> fin_cases y <;>
    simp [cutEndpoint_zero_zero, cutEndpoint_one_zero, cutEndpoint_zero_one,
      cutEndpoint_one_one, min_eq_left h, max_eq_right h, intervalStep]

/-- 切断点より右の端点の四角形は横方向だけに変わる。 -/
lemma cutEndpoint_of_ge {n : ℕ} (k i : Fin (n + 1)) (h : k ≤ i) (x y : Fin 2) :
    cutEndpoint k i x y = intervalStep k i h x := by
  fin_cases x <;> fin_cases y <;>
    simp [cutEndpoint_zero_zero, cutEndpoint_one_zero, cutEndpoint_zero_one,
      cutEndpoint_one_one, min_eq_right h, max_eq_left h, intervalStep]

/-- 順序を持つ二つの Ar 対象を結ぶ単調な辺。 -/
def arIntervalOrder {n : ℕ} (a b : Ar.{u} n) (h : a ≤ b) : ULift.{u} (Fin 2) →o Ar.{u} n where
  toFun x := if x.down = 0 then a else b
  monotone' x y hxy := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    fin_cases x <;> fin_cases y <;> simp_all

/-- 指定した順序辺を Ar の nerve 内の標準単体の射にする。 -/
def arIntervalEdge {n : ℕ} (a b : Ar.{u} n) (h : a ≤ b) :
    (Δ[1] : SSet.{u}) ⟶ arNerve n :=
  (stdSimplex.isoNerve 1).hom ≫ nerveMap (arIntervalOrder a b h).toFunctor

/-- 切断点を跨ぐ区間の四角形は元の gapped 条件の四角形そのもの。 -/
lemma arCutSquareAt_crossing {n : ℕ} (k : Fin (n + 1)) (a : Ar.{u} n)
    (hl : a.down.val.1 ≤ k) (hr : k ≤ a.down.val.2) :
    arCutSquareAt k a = arSquare a.down.val.1 k k a.down.val.2 hl le_rfl hr := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · exact cutEndpoint_of_le k a.down.val.1 hl _ _
  · exact cutEndpoint_of_ge k a.down.val.2 hr _ _

/-- 切断点より左の区間の四角形は横の辺が恒等な退化四角形。 -/
lemma arCutSquareAt_left {n : ℕ} (k : Fin (n + 1)) (a : Ar.{u} n)
    (h : a.down.val.2 ≤ k) :
    arCutSquareAt k a = identityPushoutShape false ≫
      arIntervalEdge a (arObj k k le_rfl) ⟨a.down.property.trans h, h⟩ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change cutEndpoint k a.down.val.1 (s.1 r) (s.2 r) =
      (if s.2 r = 0 then a else arObj k k le_rfl).down.val.1
    rw [cutEndpoint_of_le k _ (a.down.property.trans h)]
    change (if s.2 r = 0 then a.down.val.1 else k) = _
    split <;> rfl
  · change cutEndpoint k a.down.val.2 (s.1 r) (s.2 r) =
      (if s.2 r = 0 then a else arObj k k le_rfl).down.val.2
    rw [cutEndpoint_of_le k _ h]
    change (if s.2 r = 0 then a.down.val.2 else k) = _
    split <;> rfl

/-- 切断点より右の区間の四角形は縦の辺が恒等な退化四角形。 -/
lemma arCutSquareAt_right {n : ℕ} (k : Fin (n + 1)) (a : Ar.{u} n)
    (h : k ≤ a.down.val.1) :
    arCutSquareAt k a = identityPushoutShape true ≫
      arIntervalEdge (arObj k k le_rfl) a ⟨h, h.trans a.down.property⟩ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change cutEndpoint k a.down.val.1 (s.1 r) (s.2 r) =
      (if s.1 r = 0 then arObj k k le_rfl else a).down.val.1
    rw [cutEndpoint_of_ge k _ h]
    change (if s.1 r = 0 then k else a.down.val.1) = _
    split <;> rfl
  · change cutEndpoint k a.down.val.2 (s.1 r) (s.2 r) =
      (if s.1 r = 0 then arObj k k le_rfl else a).down.val.2
    rw [cutEndpoint_of_ge k _ (h.trans a.down.property)]
    change (if s.1 r = 0 then k else a.down.val.2) = _
    split <;> rfl

end SerrePositivity.KST.SConstruction

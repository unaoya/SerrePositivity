module

public import SerrePositivity.KST.Descent.CoincidenceLocus
public import SerrePositivity.KST.Descent.ClosedCoproduct
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# 一致中心の外における切断の像の交わり

## 概要
切断の二つの像が同じ点を含む場合を、スキームの引き戻しを通して一致場所へ移す。
これにより、一致中心の外では制限した切断の像が互いに素になる。

## 方針
二つの原像点の組を実際のスキームの引き戻しへ持ち上げる。
切断の恒等式から二射影を等しくし、等化子による既存の一致場所の判定を適用する。

## 規約
点写像の等しさからスキームの射の等しさを直接推論しない。
切断の恒等式と引き戻しの普遍性を使う。

## 使われ方
論文 定理 3.1 の軌道射の、中心の補集合上での同型性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y : Over S} {I : Type u}

/-- 概要：一致場所の外では二切断の像が同じ点を含むなら添字は等しい（定理 3.1）。
方針：共通の像を持つ点を引き戻しへ持ち上げ、切断の式から共通の制限を構成する。
規約：相異なる二つの源点を許す。単なる点写像の一致による等化子判定ではない。
使われ方：中心の補集合上での軌道成分の互いに素な像。 -/
theorem eq_index_of_equal_section_points_outside (p : Y ⟶ X)
    (sections : I → (X ⟶ Y)) (section_identity : ∀ i, sections i ≫ p = 𝟙 X)
    {i j : I} (x y : X.left) (equal_image : (sections i).left x = (sections j).left y)
    (outside : x ∉ coincidenceLocus sections) : i = j := by
  let a := (sections i).left
  let b := (sections j).left
  let P := pullback a b
  have ha : a ≫ p.left = 𝟙 X.left := congrArg (fun k ↦ k.left) (section_identity i)
  have hb : b ≫ p.left = 𝟙 X.left := congrArg (fun k ↦ k.left) (section_identity j)
  have projections : pullback.fst a b = pullback.snd a b := by
    have h := congrArg (fun k ↦ k ≫ p.left) (pullback.condition (f := a) (g := b))
    simpa only [Category.assoc, ha, hb, Category.comp_id] using h
  let W : Over S := Over.mk (pullback.fst a b ≫ X.hom)
  let v : W ⟶ X := Over.homMk (pullback.fst a b)
  have agreement : v ≫ sections i = v ≫ sections j := by
    apply (Over.forget S).map_injective
    change pullback.fst a b ≫ a = pullback.fst a b ≫ b
    exact (pullback.condition (f := a) (g := b)).trans
      (congrArg (fun k ↦ k ≫ b) projections.symm)
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := a) (g := b) x y equal_image
  apply eq_index_of_common_restriction_outside sections v agreement w
  change pullback.fst a b w ∉ coincidenceLocus sections
  rwa [hw]

/-- 概要：一致中心の逆像を避ける開集合上で切断の像は互いに素（定理 3.1）。
方針：制限射の像の等式を元の点の像の等式に戻し、前補題で添字を等しくする。
規約：開集合が中心の逆像を避ける条件を各点について明示する。
使われ方：有限閉被覆の非交和の同型補題への互いに素の入力。 -/
theorem disjoint_restricted_section_ranges_outside (p : Y ⟶ X)
    (sections : I → (X ⟶ Y)) (section_identity : ∀ i, sections i ≫ p = 𝟙 X)
    (U : Y.left.Opens) (outside : ∀ y : U, p.left (U.ι y) ∉ coincidenceLocus sections) :
    Pairwise fun i j ↦
      Disjoint (Set.range ((sections i).left ∣_ U)) (Set.range ((sections j).left ∣_ U)) := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, hx⟩ := hz
  obtain ⟨y, hy⟩ := hz'
  let xi := ((sections i).left ⁻¹ᵁ U).ι x
  let yj := ((sections j).left ⁻¹ᵁ U).ι y
  have hi : (sections i).left xi = U.ι z := by
    change (((sections i).left ⁻¹ᵁ U).ι ≫ (sections i).left) x = U.ι z
    rw [← morphismRestrict_ι, Scheme.Hom.comp_apply, hx]
  have hj : (sections j).left yj = U.ι z := by
    change (((sections j).left ⁻¹ᵁ U).ι ≫ (sections j).left) y = U.ι z
    rw [← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
  apply different
  apply eq_index_of_equal_section_points_outside p sections section_identity xi yj
    (hi.trans hj.symm)
  have h : p.left ((sections i).left xi) = xi := by
    rw [← Scheme.Hom.comp_apply]
    change (sections i ≫ p).left xi = xi
    rw [section_identity i]
    rfl
  rw [hi] at h
  rw [← h]
  exact outside z

/-- 概要：被約な終域で中心の外の切断の非交和は同型（論文 定理 3.1）。
方針：制限した切断の像の互いに素と被覆を証明し、有限閉被覆の同型補題を適用する。
規約：section の像の被覆条件は明示し、幾何的推移性からの供給は別に必要。
使われ方：軌道射の中心の補集合上の同型性への接続。 -/
theorem restrictedSectionCoproduct_isIso [Finite I] [IsReduced Y.left]
    (p : Y ⟶ X) [IsSeparated p.left]
    (sections : I → (X ⟶ Y)) (section_identity : ∀ i, sections i ≫ p = 𝟙 X)
    (covering : ⋃ i, Set.range (sections i).left = Set.univ)
    (U : Y.left.Opens) (outside : ∀ y : U, p.left (U.ι y) ∉ coincidenceLocus sections) :
    IsIso (Sigma.desc fun i ↦ (sections i).left ∣_ U) := by
  have (i : I) : IsClosedImmersion (sections i).left :=
    closedImmersion_of_section p.left (sections i).left
      (congrArg (fun k ↦ k.left) (section_identity i))
  apply finiteClosedCoproduct_isIso _
    (disjoint_restricted_section_ranges_outside p sections section_identity U outside)
  apply Set.eq_univ_iff_forall.mpr
  intro y
  have hy : U.ι y ∈ ⋃ i, Set.range (sections i).left := by
    rw [covering]
    exact Set.mem_univ _
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hy
  apply Set.mem_iUnion.mpr
  refine ⟨i, ⟨x, ?_⟩, ?_⟩
  · change (sections i).left x ∈ U
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe (sections i).left U _).trans hx

end SerrePositivity.KST.Descent

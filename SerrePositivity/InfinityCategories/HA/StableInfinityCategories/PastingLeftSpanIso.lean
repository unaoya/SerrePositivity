module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftSubcomplex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PastingRightCocone

/-! # 左 span の標準形

概要：左 span は標準ホーン Λ[2,0] と同型である。
方針：横座標を一つ上げて右 span と同定し、その標準形を使う。
規約：左の下辺の終点は (1,0)。使われ方：S4 の左四角形の余極限判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：横座標を一つ下げ、零で止める単調写像。
方針：有限順序集合の比較を検査する。
規約：右 span から左 span へ戻す写像。使われ方：span の同型の逆射。 -/
def pastingLeftLowerOrderHom : Fin 3 →o Fin 3 where
  toFun x := ⟨x.val - 1, by have := x.isLt; omega⟩
  monotone' _ _ h := Nat.sub_le_sub_right h 1

/-- 概要：右 span から左 span への横座標の単体作用。
方針：単調写像を標準単体の射にする。
規約：縦座標は変えない。使われ方：左 span の同型。 -/
def pastingLeftLowerSimplex {n : SimplexCategoryᵒᵖ} (x : (Δ[2] : SSet.{u}).obj n) :
    (Δ[2] : SSet.{u}).obj n :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingLeftLowerOrderHom.comp (stdSimplex.objEquiv x).toOrderHom))

/-- 概要：横座標を一つ上げ、二で止める単調写像。
方針：頂点番号に一を足した値と二の最小値を取る。
規約：左 span 上では平行移動。使われ方：右 span との比較。 -/
def pastingLeftRaiseOrderHom : Fin 3 →o Fin 3 where
  toFun x := ⟨min (x.val + 1) 2, by omega⟩
  monotone' _ _ h := min_le_min_right 2 (Nat.add_le_add_right h 1)

/-- 概要：左 span の横座標を一つ右へ移す単体作用。
方針：単調写像との後合成を使う。
規約：全次数に自然。使われ方：左 span の同型。 -/
def pastingLeftRaiseSimplex {n : SimplexCategoryᵒᵖ} (x : (Δ[2] : SSet.{u}).obj n) :
    (Δ[2] : SSet.{u}).obj n :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingLeftRaiseOrderHom.comp (stdSimplex.objEquiv x).toOrderHom))

/-- 概要：左の span を右 span へ写す。
方針：横座標を一つ上げ、縦座標を保つ。
規約：横座標二は元の span に存在しない。使われ方：左 span の標準形。 -/
def pastingLeftSpanToRight : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  app n := ↾fun s ↦ ⟨⟨(pastingLeftRaiseSimplex s.val.val.1, s.val.val.2), by
    intro j hx hy
    have hz := s.val.property j hy
    change pastingLeftRaiseOrderHom ((stdSimplex.objEquiv s.val.val.1).toOrderHom j) = 2 at hx
    rw [hz] at hx
    exact (by decide : pastingLeftRaiseOrderHom 0 ≠ 2) hx⟩, by
    intro j
    exact (by decide : ∀ x : Fin 3, pastingLeftRaiseOrderHom x ≠ 0) _⟩
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：右 span を左 span へ写す。
方針：横座標を一つ下げ、縦座標を保つ。
規約：縦座標を保つ。使われ方：左 span の標準形の逆射。 -/
def pastingRightSpanToLeft : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan : SSet.{u}) where
  app n := ↾fun s ↦ ⟨⟨(pastingLeftLowerSimplex s.val.val.1, s.val.val.2), by
    intro j hy
    have hn : (stdSimplex.objEquiv s.val.val.1).toOrderHom j ≠ 2 := by
      intro hx
      exact s.val.property j hx hy
    exact (by decide : ∀ x : Fin 3, x ≠ 2 → pastingLeftLowerOrderHom x = 0) _ hn⟩, by
    intro j
    exact (by decide : ∀ x : Fin 3, pastingLeftLowerOrderHom x ≠ 2) _⟩
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：左 span と右 span は同型。
方針：横座標の二つの変換が各三頂点上で互いに逆であることを検査する。
規約：単体集合としての同型。使われ方：標準 span との比較。 -/
def pastingLeftSpanRightIso : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  hom := pastingLeftSpanToRight
  inv := pastingRightSpanToLeft
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      exact (by decide : ∀ x : Fin 3, x ≠ 2 →
        pastingLeftLowerOrderHom (pastingLeftRaiseOrderHom x) = x) (s.val.val.1 j) (s.property j)
    · rfl
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      exact (by decide : ∀ x : Fin 3, x ≠ 0 →
        pastingLeftRaiseOrderHom (pastingLeftLowerOrderHom x) = x) (s.val.val.1 j) (s.property j)
    · rfl

/-- 概要：標準 span と長方形の左 span の同型。
方針：右 span との同型を標準ホーンの同型と合成する。
規約：始域は Λ[2,0]。使われ方：左四角形の押し出し判定。 -/
def pastingLeftSpanIso : (horn 2 0 : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso ≪≫ pastingLeftSpanRightIso.symm

/-- 概要：左 span の標準形の包含は左四角形の span の包含である。
方針：右 span の包含に横座標を下げる写像を合成し、二つの面写像を比較する。
規約：左四角形は面 δ₂。使われ方：左四角形の押し出し余錐との厳密な比較。 -/
lemma pastingLeftSpanIso_hom_ι :
    pastingLeftSpanIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  let L : (Δ[2] : SSet.{u}) ⟶ Δ[2] :=
    stdSimplex.map (SimplexCategory.mkHom pastingLeftLowerOrderHom)
  have hL : pastingRightSpanToLeft ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ (L ▷ Δ[1]) := rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom ≫ pastingRightSpanToLeft) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι = _
  rw [Category.assoc, hL]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι (L ▷ Δ[1])]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι),
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingRightSpanIso_hom_ι]
  rw [Category.assoc, ← comp_whiskerRight]
  have hδ : stdSimplex.δ (0 : Fin 3) ≫ L = stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hδ]


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

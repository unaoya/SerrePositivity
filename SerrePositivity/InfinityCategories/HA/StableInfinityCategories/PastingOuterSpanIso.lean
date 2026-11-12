module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingOuterBase
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PastingRightCocone

/-! # 外側 span の標準形

概要：外側 span は標準ホーン Λ[2,0] と同型である。
方針：横座標零を一へ動かして右 span と同定し、その標準形を使う。
規約：外側の下辺の終点は (2,0)。使われ方：S4 の外側の余極限判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：横座標二を保ち、それ以外を零へ送る単調写像。
方針：有限順序集合の比較を検査する。
規約：右 span から外側 span へ戻す写像。使われ方：span の同型の逆射。 -/
def pastingOuterLowerOrderHom : Fin 3 →o Fin 3 where
  toFun x := if x = 2 then 2 else 0
  monotone' := by decide

/-- 概要：右 span から外側 span への横座標の単体作用。
方針：単調写像を標準単体の射にする。
規約：縦座標は変えない。使われ方：外側 span の同型。 -/
def pastingOuterLowerSimplex {n : SimplexCategoryᵒᵖ} (x : (Δ[2] : SSet.{u}).obj n) :
    (Δ[2] : SSet.{u}).obj n :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingOuterLowerOrderHom.comp (stdSimplex.objEquiv x).toOrderHom))

/-- 概要：外側 span を右 span へ写す。
方針：横座標零を一へ動かし、二を保つ。
規約：両方とも三頂点の全部分図式。使われ方：外側 span の標準形。 -/
def pastingOuterSpanToRight : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  app n := ↾fun s ↦ ⟨⟨(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRaiseSimplex
      ((SSet.const (stdSimplex.obj₀Equiv.symm 1) : Δ[0] ⟶ Δ[1]).app n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 (n.unop.len + 1)).symm (OrderHom.const _ 0))) s.val.val.1,
      s.val.val.2), by
    intro j hx hy
    have hz := s.val.property j hy
    change max ((stdSimplex.objEquiv s.val.val.1).toOrderHom j) (1 : Fin 3) = 2 at hx
    rw [hz] at hx
    exact (by decide : max (0 : Fin 3) 1 ≠ 2) hx⟩, by
    intro j
    exact (by decide : ∀ x : Fin 3, max x 1 ≠ 0) _⟩
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

/-- 概要：右 span を外側 span へ写す。
方針：横座標一を零へ動かし、二を保つ。
規約：縦座標を保つ。使われ方：外側 span の標準形の逆射。 -/
def pastingRightSpanToOuter : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan : SSet.{u}) where
  app n := ↾fun s ↦ ⟨⟨(pastingOuterLowerSimplex s.val.val.1, s.val.val.2), by
    intro j hy
    have hn : (stdSimplex.objEquiv s.val.val.1).toOrderHom j ≠ 2 := by
      intro hx
      exact s.val.property j hx hy
    change pastingOuterLowerOrderHom _ = 0
    simp only [pastingOuterLowerOrderHom, OrderHom.coe_mk, ite_eq_right_iff]
    intro hx
    exact False.elim (hn hx)⟩, by
    intro j
    exact (by decide : ∀ x : Fin 3, pastingOuterLowerOrderHom x ≠ 1) _⟩
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

/-- 概要：外側 span と右 span は同型。
方針：横座標の二つの変換が各三頂点上で互いに逆であることを検査する。
規約：単体集合としての同型。使われ方：標準 span との比較。 -/
def pastingOuterSpanRightIso : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  hom := pastingOuterSpanToRight
  inv := pastingRightSpanToOuter
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
      exact (by decide : ∀ x : Fin 3, x ≠ 1 →
        pastingOuterLowerOrderHom (max x 1) = x) (s.val.val.1 j) (s.property j)
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
        max (pastingOuterLowerOrderHom x) 1 = x) (s.val.val.1 j) (s.property j)
    · rfl

/-- 概要：標準 span と長方形の外側 span の同型。
方針：右 span との同型を標準ホーンの同型と合成する。
規約：始域は Λ[2,0]。使われ方：外側四角形の押し出し判定。 -/
def pastingOuterSpanIso : (horn 2 0 : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso ≪≫ pastingOuterSpanRightIso.symm

/-- 概要：外側 span の標準形の包含は外側四角形の span の包含である。
方針：右 span の包含に横座標を下げる写像を合成し、二つの面写像を比較する。
規約：外側四角形は面 δ₁。使われ方：外側の押し出し余錐との厳密な比較。 -/
lemma pastingOuterSpanIso_hom_ι :
    pastingOuterSpanIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  let L : (Δ[2] : SSet.{u}) ⟶ Δ[2] :=
    stdSimplex.map (SimplexCategory.mkHom pastingOuterLowerOrderHom)
  have hL : pastingRightSpanToOuter ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ (L ▷ Δ[1]) := rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom ≫ pastingRightSpanToOuter) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι = _
  rw [Category.assoc, hL]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι (L ▷ Δ[1])]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι),
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingRightSpanIso_hom_ι]
  rw [Category.assoc, ← comp_whiskerRight]
  have hδ : stdSimplex.δ (0 : Fin 3) ≫ L = stdSimplex.δ (1 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hδ]

/-- 概要：四頂点図式から標準の外側 span への coslice 制限は trivial Kan fibration。
方針：外側 span への right anodyne な制限を標準形の同型で移す。
規約：値域は quasicategory。使われ方：外側の余極限判定。 -/
lemma pastingOuterBaseRestrict_standardSpan_trivialKanFibration {X : SSet.{u}}
    [Quasicategory X] (p : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p (pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι)) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_trivialKanFibration p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_subcomplexIso p _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan pastingOuterSpanIso

/-- 概要：四頂点図式の余錐は標準の外側 span で余極限性を判定できる。
方針：制限の trivial Kan fibration による始対象性の保存と反映を使う。
規約：余錐頂点は変えない。使われ方：貼り合わせの外側比較。 -/
lemma pastingOuterBase_isColimitCone_iff_standardSpan {X : SSet.{u}} [Quasicategory X]
    {p : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict (pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι)) := by
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p (pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι))).isInitialVertex_iff c

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

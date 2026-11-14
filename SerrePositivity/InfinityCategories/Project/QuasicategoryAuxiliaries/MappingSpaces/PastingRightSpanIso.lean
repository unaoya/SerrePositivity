module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PastingCorner
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PastingRightSpanMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 右の部分図式と標準 span の同型

概要：右の三頂点部分と Λ[2,0] は単体集合として同型。
方針：右下の横辺と中央の縦辺を pushout で貼り、符号化との両逆性を確認する。
規約：0→1 は下辺、0→2 は縦辺。
使われ方：S4 の部分長方形の余錐を標準押し出しの余錐へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：右の span の下側の横辺。
方針：右四角形の下辺を、二つの部分複体の条件に持ち上げる。
規約：(1,0)→(2,0)。
使われ方：標準 span の第一辺。 -/
def pastingRightSpanBottom : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) := by
  let f : (Δ[1] : SSet.{u}) ⟶ Δ[2] ⊗ Δ[1] :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (stdSimplex.δ (0 : Fin 3) ▷ Δ[1])
  refine { app := fun n ↦ ↾fun s ↦ ⟨⟨f.app n s, ?_⟩, ?_⟩, naturality := ?_ }
  · intro j _
    exact (by decide : (0 : Fin 2) ≠ 1)
  · intro j
    change ((stdSimplex.objEquiv s).toOrderHom j).succ ≠ 0
    exact Fin.succ_ne_zero _
  · intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · apply stdSimplex.ext
      intro j
      rfl

/-- 概要：右の span の中央の縦辺。
方針：右四角形の左辺を部分複体へ持ち上げる。
規約：(1,0)→(1,1)。
使われ方：標準 span の第二辺。 -/
def pastingRightSpanVertical : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) := by
  let f : (Δ[1] : SSet.{u}) ⟶ Δ[2] ⊗ Δ[1] :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (stdSimplex.δ (0 : Fin 3) ▷ Δ[1])
  refine { app := fun n ↦ ↾fun s ↦ ⟨⟨f.app n s, ?_⟩, ?_⟩, naturality := ?_ }
  · intro j h
    exact ((by decide : (1 : Fin 3) ≠ 2) h).elim
  · intro j
    exact (by decide : (1 : Fin 3) ≠ 0)
  · intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · apply stdSimplex.ext
      intro j
      rfl

/-- 概要：下辺を長方形へ含めると元の右下の横辺。
方針：部分型の値を取る。
規約：射の厳密な等式。使われ方：辺の貼り合わせの計算。 -/
lemma pastingRightSpanBottom_ι :
    pastingRightSpanBottom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) := rfl

/-- 概要：縦辺を長方形へ含めると元の中央の縦辺。
方針：部分型の値を取る。
規約：射の厳密な等式。使われ方：辺の貼り合わせの計算。 -/
lemma pastingRightSpanVertical_ι :
    pastingRightSpanVertical ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) := rfl

/-- 概要：右の span の二辺は始点を共有する。
方針：長方形への包含の単射性と零頂点での値を使う。
規約：厳密な射の等式。使われ方：標準 span の pushout の貼り合わせ。 -/
lemma pastingRightSpanEdges_source :
    stdSimplex.δ (1 : Fin 2) ≫ pastingRightSpanBottom.{u} =
      stdSimplex.δ (1 : Fin 2) ≫ pastingRightSpanVertical := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι)).1
  simp only [Category.assoc, pastingRightSpanBottom_ι, pastingRightSpanVertical_ι]
  exact SSet.yonedaEquiv.injective (Prod.ext (by decide) (by decide))

/-- 概要：標準 span から右の三頂点部分への射。
方針：二本の辺を共通の始点で貼る。
規約：第一辺を下辺、第二辺を縦辺へ送る。
使われ方：符号化の逆射。 -/
def pastingRightSpanFromHorn : (horn 2 0 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) :=
  horn₂₀.isPushout.desc pastingRightSpanBottom pastingRightSpanVertical pastingRightSpanEdges_source

/-- 概要：標準 span の第一辺は右下の横辺へ移る。
方針：pushout の第一包含の式を使う。
規約：0→1 の辺。使われ方：右四角形の span との照合。 -/
lemma pastingRightSpanFromHorn_left :
    horn₂₀.ι₀₁ ≫ pastingRightSpanFromHorn.{u} = pastingRightSpanBottom :=
  horn₂₀.isPushout.inl_desc _ _ _

/-- 概要：標準 span の第二辺は中央の縦辺へ移る。
方針：pushout の第二包含の式を使う。
規約：0→2 の辺。使われ方：右四角形の span との照合。 -/
lemma pastingRightSpanFromHorn_right :
    horn₂₀.ι₀₂ ≫ pastingRightSpanFromHorn.{u} = pastingRightSpanVertical :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- 概要：符号化を標準二単体へ含めると長方形上の符号化の制限。
方針：部分複体への持ち上げの定義を使う。
規約：射の厳密な等式。使われ方：二本の辺での逆性の検証。 -/
lemma pastingRightSpanToHorn_ι :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn.{u} ≫ (horn 2 0).ι =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSpanCodeMap := rfl

private lemma bottom_code :
    pastingRightSpanBottom.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn = horn₂₀.ι₀₁ := by
  apply (cancel_mono (horn 2 0).ι).1
  rw [Category.assoc, pastingRightSpanToHorn_ι]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSpanCodeMap]
  rw [← Category.assoc pastingRightSpanBottom
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSpanCodeMap, pastingRightSpanBottom_ι]
  exact SSet.yonedaEquiv.injective (by decide)

private lemma vertical_code :
    pastingRightSpanVertical.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn = horn₂₀.ι₀₂ := by
  apply (cancel_mono (horn 2 0).ι).1
  rw [Category.assoc, pastingRightSpanToHorn_ι]
  rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSpanCodeMap]
  rw [← Category.assoc pastingRightSpanVertical
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSpanCodeMap, pastingRightSpanVertical_ι]
  exact SSet.yonedaEquiv.injective (by decide)

/-- 概要：右の三頂点部分と標準 span ホーンの同型。
方針：二辺の貼り合わせと符号化がホーン上で逆であることを示し、符号化の単射性で他方の逆性を得る。
規約：順方向は標準 span から部分図式へ向かう。
使われ方：S4 の右四角形の普遍性への移送。 -/
def pastingRightSpanIso : (horn 2 0 : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  hom := pastingRightSpanFromHorn
  inv := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn
  hom_inv_id := by
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, pastingRightSpanFromHorn_left, bottom_code, Category.comp_id]
    · rw [← Category.assoc, pastingRightSpanFromHorn_right, vertical_code, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn).1
    rw [Category.assoc]
    have h : pastingRightSpanFromHorn ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanToHorn = 𝟙 (horn 2 0 : SSet.{u}) := by
      apply horn₂₀.isPushout.hom_ext
      · rw [← Category.assoc, pastingRightSpanFromHorn_left, bottom_code, Category.comp_id]
      · rw [← Category.assoc, pastingRightSpanFromHorn_right, vertical_code, Category.comp_id]
    rw [h, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

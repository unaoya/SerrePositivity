module

public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import SerrePositivity.KST.Descent.SchemeFacts
public import SerrePositivity.KST.Descent.BlowupSequenceData

/-!
# 二つの閉部分による被覆の抽象 blowup 正方形

## 概要
被約スキームを二つの閉部分が覆うとき、その実際の交わりを抽象 blowup 正方形とする。

## 方針
一方の閉部分の補集合では、他方の閉埋め込みが点全射となることから同型性を示す。

## 規約
交わりには実際の引き戻しを用い、被約化で置き換えない。

## 使われ方
論文 補題 3.3・定理 3.1 の閉和から被約スキームの既約成分へ移る帰納。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：被約な開集合を像が覆う閉埋め込みの制限は同型（論文 補題 3.3）。
方針：制限後の点全射性を直接示し、被約な終域への全射閉埋め込みの判定を使う。
規約：終域の被約性を明示する。
使われ方：二つの閉部分が覆う場合の補集合上の同型性。 -/
theorem closedImmersion_restrict_isIso_of_subset_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [IsReduced Y] (U : Y.Opens)
    (covered : (U : Set Y) ⊆ Set.range f) : IsIso (f ∣_ U) := by
  have : Surjective (f ∣_ U) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := covered y.property
    have hxU : x ∈ f ⁻¹ᵁ U := by
      change f x ∈ U
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxU⟩, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe f U _).trans hx
  exact isIso_of_surjective_closedImmersion (f ∣_ U)

/-- 概要：二つの閉部分の実際の被覆は抽象 blowup 正方形を与える（論文 補題 3.3）。
方針：閉埋め込みの固有性と、他方の閉部分の外での同型性を組み合わせる。
規約：被約性は被覆される終域に課し、二つの閉部分や交わりには要求しない。
使われ方：公理 (2) から閉和に対する降下の長完全列を得る幾何入力。 -/
noncomputable def closedCoverAbstractBlowup {S : Scheme.{u}} {X Y Z : FiniteTypeSchemes S}
    [IsReduced X.obj.left] (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ) :
    AbstractBlowupSquare S := by
  let U : X.obj.left.Opens :=
    ⟨(Set.range j.hom.left)ᶜ, j.hom.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have covered : (U : Set X.obj.left) ⊆ Set.range i.hom.left := by
    intro x hx
    have h : x ∈ Set.range i.hom.left ∪ Set.range j.hom.left := by
      rw [covering]
      exact Set.mem_univ x
    exact h.resolve_right hx
  exact abstractBlowupOfClosedImmersion i j U rfl
    (closedImmersion_restrict_isIso_of_subset_range i.hom.left U covered)

/-- 概要：自然な blowup 列から二つの閉部分の被覆の全次数列を得る（論文 補題 3.3）。
方針：被覆から構成した実際の抽象 blowup 正方形に指定データを適用する。
規約：境界と完全性を保持し、次数ごとの通常の引き戻しで実降下を置き換えない。
使われ方：閉和から既約成分への還元における全次数の貼り合わせ。 -/
noncomputable def NaturalBlowupSequences.closedCoverSequence {S : Scheme.{u}}
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) {X Y Z : FiniteTypeSchemes S} [IsReduced X.obj.left]
    (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ) (H : Coefficient) :
    SquareMayerVietoris L H (closedImmersionSquare i j) :=
  data.sequence (closedCoverAbstractBlowup i j covering) H

end SerrePositivity.KST.Descent

module

public import SerrePositivity.KST.DerivedGeometry.SubobjectEpiEmbedding
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
概要：固定した対象の全ての商を同型まで含む小さい対象族を構成する。
方針：反対圏の部分対象の小さい集合から、実際の代表対象と全射を取る。
規約：商の代表の存在を未証明の構造体フィールドとして置かない。
使われ方：Stacks Lemma 19.12.1・19.12.2、TT §3・§8、Toën §3.2 の小さい試験集合の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：固定した対象の商の小さい代表族。
方針：反対圏の部分対象集合を universe 縮小する。
規約：対象の同型類ではなく実際の対象を返す。
使われ方：Stacks 19.12.2、TT §3 の次数ごとの商の代表。
-/
def smallQuotientFamily (Q : C) (s : Shrink.{w} (Subobject (op Q))) : C :=
  unop ((equivShrink (Subobject (op Q))).symm s : Cᵒᵖ)

/--
概要：商の小さい代表への標準の全射。
方針：反対圏の部分対象の包含を反転する。
規約：元の固定した対象を始域とする。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の固定された商の模型。
-/
def smallQuotientProjection (Q : C) (s : Shrink.{w} (Subobject (op Q))) :
    Q ⟶ smallQuotientFamily Q s :=
  ((equivShrink (Subobject (op Q))).symm s).arrow.unop

/--
概要：小さい商の模型への標準射は全射。
方針：部分対象の包含の単射性を反転する。
規約：アーベル圏の実際の全射。
使われ方：Stacks 19.12.2、TT §3 の商の小さい代表族。
-/
instance smallQuotientProjection_epi (Q : C) (s : Shrink.{w} (Subobject (op Q))) :
    Epi (smallQuotientProjection Q s) := by
  dsimp [smallQuotientProjection]
  infer_instance

/--
概要：固定した対象の任意の商は小さい代表族のいずれかと同型。
方針：全射を反対圏の部分対象として取り、代表の underlyingIso を反転する。
規約：商の存在は入力された全射で表す。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の非輪状試験集合の小ささ。
-/
lemma exists_smallQuotientFamily_iso {Q N : C} (p : Q ⟶ N) [Epi p] :
    ∃ s : Shrink.{w} (Subobject (op Q)), Nonempty (smallQuotientFamily Q s ≅ N) := by
  refine ⟨equivShrink _ (Subobject.mk p.op), ?_⟩
  let e := (Subobject.underlyingIso p.op).unop.symm
  have hs : (equivShrink (Subobject (op Q))).symm
      (equivShrink _ (Subobject.mk p.op)) = Subobject.mk p.op :=
    (equivShrink _).symm_apply_apply _
  dsimp only [smallQuotientFamily]
  rw [hs]
  exact ⟨e⟩

end SerrePositivity.KST.DerivedGeometry

module

public import SerrePositivity.KST.DerivedGeometry.SmallGeneratorEpiCover
public import SerrePositivity.KST.DerivedGeometry.SubobjectEpiEmbedding
public import SerrePositivity.KST.DerivedGeometry.CoproductEmbeddingRetraction

/-!
概要：終域の部分対象集合の埋め込みを使い、小さい全射部分対象の直和の添字を統一する。
方針：直和の明示的な縮約を合成し、像を取る。
規約：上界となる添字集合を実際の集合の埋め込みで与える。
使われ方：Stacks Lemma 19.12.1・19.12.2、TT §3・§8、Toën §3.2 の試験族の濃度管理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：全射による部分対象集合の埋め込みを小さい universe 上で表す。
方針：構成済みの部分対象の埋め込みを universe 縮小の同値で挟む。
規約：始域・終域双方の小さい部分対象集合。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の固定された対象による上界。
-/
def smallSubobjectEpiEmbedding {Q N : C} (q : Q ⟶ N) [Epi q] :
    Shrink.{w} (Subobject N) ↪ Shrink.{w} (Subobject Q) :=
  (equivShrink (Subobject N)).symm.toEmbedding |>.trans (subobjectEpiEmbedding q)
    |>.trans (equivShrink (Subobject Q)).toEmbedding

/--
概要：商の部分対象の部分対象集合を、元の固定した対象の部分対象集合へ埋め込む。
方針：単射による部分対象の埋め込みと全射による構成済みの埋め込みを合成する。
規約：小さい universe 上の実際の集合の埋め込み。
使われ方：Stacks 19.12.2、TT §3 の核を覆う部分対象の統一した上界。
-/
def smallSubquotientEmbedding {Q N S : C} (q : Q ⟶ N) [Epi q] (i : S ⟶ N) [Mono i] :
    Shrink.{w} (Subobject S) ↪ Shrink.{w} (Subobject Q) :=
  (equivShrink (Subobject S)).symm.toEmbedding
    |>.trans ⟨(Subobject.map i).obj, Subobject.map_obj_injective i⟩
    |>.trans (subobjectEpiEmbedding q)
    |>.trans (equivShrink (Subobject Q)).toEmbedding

/--
概要：固定した添字集合を上界とする生成対象の直和の商で、全射部分対象を構成する。
方針：添字集合の埋め込みの縮約を小さい全射被覆へ合成して像を取る。
規約：終域の部分対象集合の上界は集合の単射として用いる。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の小さい非輪状部分複体の各項。
-/
lemma exists_uniform_generator_epi_subobject (G : C) (hG : IsSeparator G)
    {M N : C} (p : M ⟶ N) [Epi p] {τ : Type w}
    (e : Shrink.{w} (Subobject N) ↪ τ) :
    ∃ (M' : C) (a : (∐ fun _ : τ => G) ⟶ M') (i : M' ⟶ M),
      Epi a ∧ Mono i ∧ Epi (i ≫ p) := by
  let d := coproductEmbeddingRetraction G e ≫ smallGeneratorEpiCoverMap G hG p
  have hd : Epi (d ≫ p) := by
    dsimp [d]
    rw [Category.assoc]
    infer_instance
  have he : Epi (factorThruImage d ≫ (image.ι d ≫ p)) := by
    rw [← Category.assoc, image.fac]
    exact hd
  have : Epi (image.ι d ≫ p) := epi_of_epi (factorThruImage d) (image.ι d ≫ p)
  exact ⟨image d, factorThruImage d, image.ι d, inferInstance, inferInstance, inferInstance⟩

/--
概要：終域が固定した対象の商なら、その対象だけで添字を決めた小さい全射部分対象が存在する。
方針：全射による部分対象集合の埋め込みを統一した上界へ適用する。
規約：固定した対象の部分対象集合で添字付けた生成対象の直和。
使われ方：Stacks 19.12.1・19.12.2、TT §3・§8 の小さい試験集合。
-/
lemma exists_quotient_bounded_generator_epi_subobject (G : C) (hG : IsSeparator G)
    {M N Q : C} (p : M ⟶ N) [Epi p] (q : Q ⟶ N) [Epi q] :
    ∃ (M' : C) (a : (∐ fun _ : Shrink.{w} (Subobject Q) => G) ⟶ M') (i : M' ⟶ M),
      Epi a ∧ Mono i ∧ Epi (i ≫ p) :=
  exists_uniform_generator_epi_subobject G hG p (smallSubobjectEpiEmbedding q)

end SerrePositivity.KST.DerivedGeometry

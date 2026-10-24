module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSmallness
public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplexFibers

/-!
概要：固定頂点写像の小ささから、表現可能 right fibration の次数 fiber の小ささを得る。
方針：元の slice の単体を、join の両境界を固定した写像の小さい型へ単射で入れる。
規約：Ind 側の公開小ささ補題を使い、元の slice と射影を保持する。
使われ方：元の反変 Hom の小さい空間値 straightening を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：固定頂点写像が小さい圏の元の表現可能射影は小さい次数 fiber を持つ。
方針：射影が固定する左境界と slice が固定する右境界を同時に符号化する。
規約：quasicategory 性は不要。
使われ方：小さい空間値の元の反変 Hom の構成。 -/
lemma representable_hasSmallSimplexFibers {C : SSet.{u + 1}}
    (hC : Ind.HasSmallFixedVertexMaps C) (y : C _⦋0⦌) :
    HasSmallSimplexFibers (sliceOverProjection (SSet.yonedaEquiv.symm y)) := by
  intro n b
  rcases n with ⟨⟨n⟩⟩
  let T := {f : join (Δ[n] : SSet.{u + 1}) Δ[0] ⟶ C //
    joinInl Δ[n] Δ[0] ≫ f = SSet.yonedaEquiv.symm b ∧
    joinInr Δ[n] Δ[0] ≫ f = SSet.yonedaEquiv.symm y}
  have : Small.{u} T := Ind.small_joinMaps_fixedBoundary hC _ _
  let code (s : {s : (sliceOver (SSet.yonedaEquiv.symm y)) _⦋n⦌ //
      (sliceOverProjection (SSet.yonedaEquiv.symm y)).app _ s = b}) : T :=
    ⟨s.val.val, by
      constructor
      · apply SSet.yonedaEquiv.injective
        exact s.property.trans (SSet.yonedaEquiv.apply_symm_apply b).symm
      · exact s.val.property⟩
  apply small_of_injective (f := code)
  intro s t h
  have hv : s.val.val = t.val.val := congrArg (fun z : T => z.val) h
  exact Subtype.ext (Subtype.ext hv)

/-- 概要：反転射影も同じ小さい次数 fiber を持つ。
方針：反転は各次数の写像を元の次数に再添字するだけである。
規約：全空間と底の宇宙は変更しない。
使われ方：表現可能 right fibration を left straightening へ渡す。 -/
lemma smallSimplexFibers_op {E B : SSet.{u + 1}} {p : E ⟶ B}
    (hp : HasSmallSimplexFibers p) : HasSmallSimplexFibers (SSet.opFunctor.map p) := by
  intro n b
  exact hp _ b

end SerrePositivity.InfinityCategories.F2.Presentable

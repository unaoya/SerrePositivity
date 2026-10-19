module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject

/-!
概要：部分対象格子の拡大関数の超限反復を、元の圏の連続な単射図式として実現する。
方針：反復の単調性で MonoOver の図式を作り、supremum の普遍性で極限連続性を示す。
規約：拡大関数自体の単調性は要求せず、各部分対象を含むことだけを使う。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の非輪状部分複体の超限分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {M : C} (φ : Subobject M → Subobject M) (hφ : ∀ S, S ≤ φ S) (S₀ : Subobject M)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/--
概要：部分対象の拡大関数の超限反復を MonoOver の図式として表す。
方針：部分対象の包含関係から実際の単射を取る。
規約：選択した整列型 J の全段階。
使われ方：Stacks 19.12.3、TT §3 の連続超限列。
-/
def subobjectIterationToMonoOver : J ⥤ MonoOver M where
  obj j := MonoOver.mk (transfiniteIterate φ j S₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
    (monotone_transfiniteIterate φ S₀ hφ (leOfHom f)))

/--
概要：超限反復の各部分対象の実際の対象の図式。
方針：MonoOver の図式から忘却する。
規約：部分対象格子上の反復と同じ各項を持つ。
使われ方：Stacks 19.12.3、TT §3 の完全な filtered colimit と互換な零ホモトピー。
-/
abbrev subobjectIterationFunctor : J ⥤ C :=
  subobjectIterationToMonoOver φ hφ S₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

set_option backward.defeqAttrib.useBackward true in
/--
概要：部分対象の拡大関数の超限反復は、元の圏で整列極限に連続。
方針：反復の極限段階の supremum を MonoOver の余極限へ比較する。
規約：Grothendieck アーベル圏の完全な有向余極限を用いる。
使われ方：Stacks 19.12.3、TT §3 の超限列の極限段階。
-/
instance subobjectIterationFunctor_isWellOrderContinuous :
    (subobjectIterationFunctor φ hφ S₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone
      (subobjectIterationToMonoOver φ hφ S₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ subobjectIterationToMonoOver φ hφ S₀ J) c
    dsimp [c]
    change Subobject.mk (transfiniteIterate φ m S₀).arrow =
      ⨆ j : Set.Iio m, Subobject.mk (transfiniteIterate φ j.val S₀).arrow
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit φ S₀ m hm⟩

/--
概要：真の部分対象を常に真に大きくする反復は、小さい整列長で全体へ到達する。
方針：部分対象集合の濃度より大きい整列型を選び、反復の単射性との矛盾を使う。
規約：整列長と到達段階は結論として構成する。
使われ方：Stacks 19.12.3、TT §3 の全体を尽くす超限列。
-/
lemma subobjectIteration_exists_ordinal
    (hstrict : ∀ S ≠ (⊤ : Subobject M), S < φ S) (htop : φ ⊤ = ⊤) :
    ∃ (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate φ j S₀ = ⊤ := by
  have : Nonempty (Subobject M) := ⟨⊥⟩
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject M)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have hJ : HasCardinalLT (Subobject M) (Cardinal.mk κ.ord.ToType) :=
    lt_of_lt_of_le (Order.lt_succ _) (by simp [κ])
  refine ⟨κ.ord, ?_⟩
  exact top_mem_range_transfiniteIterate φ S₀ hstrict htop
    (fun h => by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

end SerrePositivity.KST.DerivedGeometry

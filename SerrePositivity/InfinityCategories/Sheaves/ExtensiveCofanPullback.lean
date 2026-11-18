module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveIndex
public import Mathlib.CategoryTheory.Limits.VanKampen

/-!
概要：有限余積被覆の同じ引き戻し cofan と、その生成篩の引き戻しを固定する。
方針：Mathlib の有限余積の普遍性と生成篩の引き戻しの既存の法則を適用する。
  文献対応：HTT 6.2.2.6 の extensive 位相の底変換の入力。
規約：空族と任意の有限 Type u を含む。局所的な指数や追加の降下を仮定しない。
使われ方：S1 の有限積保存から全被覆篩での降下を出す逆向き。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {ι : Type u} {B : ι → C}

/-- 元の有限 cofan の各脚の引き戻しは存在する。 -/
def cofanPullbackHasPullback [FinitaryPreExtensive C] [Finite ι]
    (c : Cofan B) (hc : IsColimit c) {V : C} (f : V ⟶ c.pt) (i : ι) :
    HasPullback f (c.inj i) :=
  FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc (Discrete.mk i) f

/-- 元の脚をすべて同じ f に沿って引き戻した指定 cofan。 -/
abbrev cofanPullback (c : Cofan B) {V : C} (f : V ⟶ c.pt)
    [∀ i, HasPullback f (c.inj i)] : Cofan (fun i => pullback f (c.inj i)) :=
  Cofan.mk V (fun i => pullback.fst f (c.inj i))

/-- 既存の有限余積の普遍性は、元の指定引き戻し cofan の余極限性を与える。 -/
def cofanPullback_isColimit [FinitaryPreExtensive C] [Finite ι]
    (c : Cofan B) (hc : IsColimit c) {V : C} (f : V ⟶ c.pt)
    [∀ i, HasPullback f (c.inj i)] : IsColimit (cofanPullback c f) := by
  have hau : IsUniversalColimit c := FinitaryPreExtensive.isUniversal_finiteCoproducts hc
  apply Classical.choice
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i => ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [cofanPullback]) (by simp [pullback.condition, cofanPullback])
  exact pullback.isLimit _ _

/-- 同じ引き戻し cofan の生成篩は、元の生成篩の引き戻しそのもの。 -/
lemma cofanPullback_generatedSieve (c : Cofan B) {V : C} (f : V ⟶ c.pt)
    [∀ i, HasPullback f (c.inj i)] :
    cofanGeneratedSieve (cofanPullback c f) = (cofanGeneratedSieve c).pullback f :=
  Sieve.ofArrows_eq_pullback_of_isPullback c.inj
    (fun i => IsPullback.of_hasPullback f (c.inj i))

end SerrePositivity.InfinityCategories.Sheaves

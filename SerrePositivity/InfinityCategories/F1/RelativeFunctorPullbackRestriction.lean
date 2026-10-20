module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPullback
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPullbackSquare
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverEquivalence

/-!
概要：相対 Hom の引き戻し作用を、元の底上での始域の制限として判定する。
方針：引き戻し四角形の相対後合成の同型を合成し、相対 uncurry で同じ制限を回収する。
規約：底の初頂点写像の同値性は仮定しない。
使われ方：初頂点引き戻し作用を宇宙移送の前合成自然性で元の宇宙へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 引き戻した始域から元の始域への射を、元の底上の射として表示する。 -/
def relativeFunctorPullbackSourceMap {E B D : SSet.{u}} (p : E ⟶ B) (k : D ⟶ B) :
    Over.mk (pullback.snd p k ≫ k) ⟶ Over.mk p :=
  Over.homMk (pullback.fst p k) pullback.condition

/-- 実際の引き戻しを元の標的へ写すと、元の底上の同じ始域制限となる。 -/
lemma relativeFunctorPullback_sourceRestriction {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) :
    relativeFunctorPullback p q k ≫
      (relativeFunctorBaseChangeIso q k (pullback.snd p k)).hom =
    relativeFunctorOverPre q (relativeFunctorPullbackSourceMap p k) := by
  apply relativeFunctorUncurry_injective
  change relativeFunctorUncurry
    (relativeFunctorPullback p q k ≫ relativeFunctorBaseChangeForward q k _) = _
  rw [relativeFunctorBaseChangeForward_uncurry]
  have hk := relativeFunctorPullback_uncurry_fst p q k (𝟙 _)
  simp only [Category.id_comp] at hk
  rw [hk]
  have h := relativeFunctorOverPre_uncurry q (relativeFunctorPullbackSourceMap p k) (𝟙 _)
  change relativeFunctorUncurry (𝟙 _ ≫
    relativeFunctorOverPre q (relativeFunctorPullbackSourceMap p k)) =
    (pullback.fst p k ▷ relativeFunctorSpace q p) ≫ relativeFunctorUncurry (𝟙 _) at h
  simpa only [Category.id_comp] using h.symm

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 相対 Hom の引き戻しの同値性は、元の底上の同じ始域制限の同値性と同値。 -/
lemma relativeFunctorPullback_isQCatEquivalence_iff_sourceRestriction
    {E F B D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) [LeftFibration q] :
    IsQCatEquivalence (relativeFunctorPullback p q k) ↔
    IsQCatEquivalence (relativeFunctorOverPre q (relativeFunctorPullbackSourceMap p k)) := by
  have he : IsQCatEquivalence
      (relativeFunctorBaseChangeIso q k (pullback.snd p k)).hom := (qCatEquivalenceOfIso
    (relativeFunctorBaseChangeIso q k (pullback.snd p k))).isQCatEquivalence
  constructor
  · intro h
    simpa only [relativeFunctorPullback_sourceRestriction] using h.comp he
  · intro h
    apply he.cancel_right
    rwa [relativeFunctorPullback_sourceRestriction]

end SerrePositivity.InfinityCategories

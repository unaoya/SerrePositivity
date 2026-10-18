module

public import SerrePositivity.KST.Comparison.MonoidPointedColimit
public import SerrePositivity.KST.Comparison.StableHatGL
public import SerrePositivity.KST.Comparison.HatGLCoefficientKan
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# 安定 ĜL の実際の Kan 性

概要：安定 ĜL の台集合は有限 rank の Kan 複体の順序余極限なので Kan である。
方針：台集合への忘却の余極限保存と有限ホーンの有限表示可能性を使う。
規約：KST Lemma 2.13 の実際の安定モノイドに基点を付ける。
使われ方：π_n と安定 rank の余極限の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits SSet
open scoped Simplicial

/--
概要：有限 rank の単位基点付き ĜL から安定 ĜL への cocone。
方針：元の単体的モノイドの余極限 cocone に点付き関手を施す。
規約：基点を選び直さない。
使われ方：K-L9 の点付きホモトピー群の cocone。
-/
def stableHatGLPointedCocone (A : SimplicialObject RingCat.{u}) :
    Cocone (hatGLRankSequence A ⋙ monoidPointedFunctor) :=
  monoidPointedFunctor.mapCocone (colimit.cocone (hatGLRankSequence A))

/--
概要：安定 ĜL の点付き cocone の台集合は余極限 cocone である。
方針：単体的モノイドの台集合の順序余極限保存を使う。
規約：点付き余極限の存在を仮定せず、台集合の普遍性を直接示す。
使われ方：有限ホーンの因子分解とホモトピー群の余極限。
-/
def stableHatGLPointedCocone_underlyingIsColimit (A : SimplicialObject RingCat.{u}) :
    IsColimit (PointedSimplicialSet.forget.mapCocone (stableHatGLPointedCocone A)) :=
  isColimitOfPreserves monoidSpaceFunctor (colimit.isColimit (hatGLRankSequence A))

/--
概要：安定 ĜL の台単体集合は Kan 複体である。
方針：有限ホーンを有限 rank の段へ下ろし、その段の充填を安定対象へ合成する。
規約：元の単体的環に Kan 性の追加入力を求めない。
使われ方：KST Lemma 2.13 の安定 rank の実際のホモトピー群。
-/
instance stableHatGL_kanComplex (A : SimplicialObject RingCat.{u}) :
    KanComplex (monoidSpace (stableHatGL A)) := by
  let c := PointedSimplicialSet.forget.mapCocone (stableHatGLPointedCocone A)
  have hc : IsColimit c := stableHatGLPointedCocone_underlyingIsColimit A
  have : ∀ j, KanComplex ((hatGLRankSequence A ⋙ monoidPointedFunctor ⋙
      PointedSimplicialSet.forget).obj j) := fun j =>
    inferInstanceAs (KanComplex (hatGLSpace A j))
  let e := (AsSmall.equiv.{0, 0, u} (C := ℕ)).symm
  have : IsFiltered (AsSmall.{u} ℕ) :=
    IsFiltered.of_equivalence (AsSmall.equiv.{0, 0, u} (C := ℕ))
  let d := c.whisker e.functor
  have hd : IsColimit d := hc.whiskerEquivalence e
  rw [KanComplex.iff]
  intro n i f hf
  obtain ⟨j, t, ht⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hd hf.desc
  have : KanComplex ((e.functor ⋙ ((hatGLRankSequence A ⋙ monoidPointedFunctor) ⋙
      PointedSimplicialSet.forget)).obj j) :=
    inferInstanceAs (KanComplex (hatGLSpace A (e.functor.obj j)))
  obtain ⟨s, hs⟩ := KanComplex.hornFilling t
  have h : (horn (n + 1) i).ι ≫ (s ≫ d.ι.app j) = hf.desc := by
    rw [← Category.assoc, ← hs, ht]
  refine ⟨s ≫ d.ι.app j, fun k hk => ?_⟩
  rw [← horn.ι_ι_assoc i k hk, h]
  exact hf.ι_desc k hk

end SerrePositivity.KST.Comparison

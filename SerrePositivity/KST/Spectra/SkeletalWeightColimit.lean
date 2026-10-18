module

public import SerrePositivity.KST.Spectra.SkeletalWeightedEndTower
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：有限骨格の重みの増加余極限は元の重みである。
方針：部分複体の上限の余極限と、図式の値ごとの余極限を使う。
規約：通常の圏の余極限。Kan 性もホモトピー極限性も仮定しない。
使われ方：Goerss–Jardine VIII §1。全体の end と部分 end の塔の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.SkeletalWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の n 骨格の列を部分複体の順序関手とする。
方針：skeleton の単調性へ添字 n+1 の単調性を合成する。
規約：n は含める単体の最大次元。
使われ方：Goerss–Jardine VIII §1。骨格の余極限の順序圏での模型。 -/
def skeletonOrder (X : SSet.{u}) : ℕ →o X.Subcomplex where
  toFun n := X.skeleton (n + 1)
  monotone' _ _ h := X.skeleton.monotone (Nat.add_le_add_right h 1)

lemma iSup_skeleton_succ (X : SSet.{u}) : (⨆ n, X.skeleton (n + 1)) = ⊤ := by
  apply le_antisymm le_top
  rw [← X.iSup_skeleton, iSup_le_iff]
  intro n
  exact le_trans (X.skeleton.monotone (Nat.le_succ n))
    (le_iSup (fun m ↦ X.skeleton (m + 1)) n)

/-- 概要：単体集合の有限骨格の図式から元の単体集合への余錐。
方針：部分複体の包含を使う。
規約：この余錐の各脚は単射。
使われ方：Goerss–Jardine VIII §1。各値の骨格の余極限。 -/
def skeletonCocone (X : SSet.{u}) :
    Cocone ((skeletonOrder X).monotone.functor ⋙ Subcomplex.toSSetFunctor) where
  pt := X
  ι := { app n := (X.skeleton (n + 1)).ι }

/-- 概要：単体集合は有限骨格の通常の余極限である。
方針：部分複体の上限の余極限を単体集合へ送り、全体の部分複体と同定する。
規約：すべての単体は有限次元なので骨格の上限は全体。
使われ方：Goerss–Jardine VIII §1。部分 Tot の塔の完全性の基礎。 -/
def skeletonCoconeIsColimit (X : SSet.{u}) : IsColimit (skeletonCocone X) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone (skeletonOrder X).monotone.functor).isColimit)
      (Cocone.ext (Subcomplex.eqToIso (iSup_skeleton_succ X) ≪≫ Subcomplex.topIso X))

/-- 概要：重みはその有限骨格の図式の余極限である。
方針：各添字で単体集合の骨格の余極限へ帰着する。
規約：通常の関手圏の余極限。
使われ方：Goerss–Jardine VIII §1。重み付き end の骨格による解析。 -/
def weightCoconeIsColimit {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u}) :
    IsColimit (weightCocone W) :=
  evaluationJointlyReflectsColimits _ (fun i ↦ skeletonCoconeIsColimit (W.obj i))

end

end SerrePositivity.KST.Spectra.SkeletalWeightedEnd

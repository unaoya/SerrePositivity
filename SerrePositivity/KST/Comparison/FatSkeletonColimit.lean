module

public import SerrePositivity.KST.Comparison.FatSkeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation

/-!
# 有限骨格の順序余極限としての fat realization

概要：有限骨格の増大する順序列の余極限を、元の fat realization と同定する。
方針：部分単体集合の上限と、filtered colimit の前層への包含による保存を使う。
規約：Segal 1974 Proposition 1.6、Lemma 1.8 の無限骨格への移行の対象。
使われ方：telescope と有限骨格の順序余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：fat realization の有限骨格の増大する順序列。
方針：部分単体集合の単調関数を関手化し、単体集合へ含める。
規約：第 n 項は n 行までを含む骨格。
使われ方：無限骨格の余極限と telescope。
-/
def fatSkeletonSequence (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : ℕ ⥤ SSet.{u} :=
  (fatSkeleton_monotone F).functor ⋙ SSet.Subcomplex.toSSetFunctor

/--
概要：有限骨格の順序列から元の fat realization への余錐。
方針：各部分単体集合の包含を使う。
規約：頂点は既存の fat realization の実対象。
使われ方：無限骨格への比較の標準余錐。
-/
def fatSkeletonCocone (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : Cocone (fatSkeletonSequence F) where
  pt := fatRealization F
  ι := { app n := (fatSkeleton F n).ι }

/--
概要：fat realization は有限骨格の順序列の余極限である。
方針：全骨格の上限が全体であることと、部分単体集合の filtered colimit 保存を使う。
規約：余極限との同値を仮定せず、具体的な包含の余錐の普遍性を示す。
使われ方：Segal の無限骨格の比較の対象の同定。
-/
def fatSkeletonCoconeIsColimit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsColimit (fatSkeletonCocone F) := by
  have h : IsLUB (Set.range (fatSkeleton F)) ⊤ := by
    rw [← iSup_fatSkeleton_eq_top F]
    exact isLUB_iSup
  let c := Preorder.colimitCoconeOfIsLUB (fatSkeleton_monotone F).functor h
  have hc := isColimitOfPreserves SSet.Subcomplex.toSSetFunctor c.isColimit
  exact IsColimit.ofIsoColimit hc
    (Cocone.ext (SSet.Subcomplex.topIso (fatRealization F)) (by intro n; rfl))

end SerrePositivity.KST.Comparison

module
public import SerrePositivity.DifferentialGraded.Verdier.NullObjects

/-! # tria の生成性・Verdier 核・後続比較の型と公理監査

## 概要
tria の生成性・Verdier 核・後続比較の型と公理監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (P : ObjectProperty (TriaCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] :
    triaImage A D S ≤ P ↔ ∀ x ∈ S, P (triaRepresentable A D x) :=
  triaImage_le_iff_generators A D S P

example (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ modulePerfectOver A D S X.obj :=
  triaQuotient_isZero_iff_perfect A D S X

example (X : TriaCategory A D) :
    IsZero ((triaQuotient A D ∅).obj X) ↔ triaNull A D ∅ X :=
  triaQuotient_isZero_iff_triaNull A D ∅ X

example (S : Set D) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ≅
      triaQuotient A D S ⋙ CategoryTheory.Idempotents.toKaroubi _ :=
  triaKaroubiComparison A D S

#print axioms triaImage_le_iff_generators
#print axioms verdierQuotient_isZero_iff_retractClosure
#print axioms verdierQuotient_kernel_eq_retractClosure
#print axioms triangEnvelope_eq_retractClosure
#print axioms triaImage_retractClosure_iff_perfect
#print axioms triaQuotient_isZero_iff
#print axioms triaQuotient_isZero_iff_triaNull
#print axioms triaQuotient_isZero_iff_perfect
#print axioms triaKaroubiOrderEquivalence
#print axioms triaKaroubiComparison

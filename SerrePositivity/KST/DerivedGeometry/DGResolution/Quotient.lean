module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedGeometry.DGResolution.PretriangulationTriangles
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence

/-!
# 分解を先行させた一般の dg 商

概要：任意の dg 圏と対象集合に対し、具体的分解後の明示的 path 商を構成する。
方針：増大関手による逆像を収縮集合とし、証明済み K-flat 性を既存比較定理へ渡す。
規約：元の Hom に平坦性を課さず、分解後の商と元の Verdier 商の移送を区別する。
使われ方：Drinfeld §3.5・Thm 3.4、KST D4、K-L1b・L3 の Verdier 商。
-/

@[expose] public section
noncomputable section
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：元の収縮対象集合の増大関手による逆像。
方針：分解後の対象の像で判定する。
規約：元の集合が同型で閉じていれば、その条件をそのまま使える。
使われ方：Drinfeld §3.5、KST D4 の acyclic 対象の逆像。
-/
def nullObjects (N : Set D) : Set (Objects A D) := fun x => (augmentation A D).obj x ∈ N

/--
概要：分解後の対象を元へ戻したときの収縮条件。
方針：増大関手の対象固定性を使う。
規約：新たな対象条件は加えない。
使われ方：Drinfeld §3.5 の逆像部分圏。
-/
lemma mem_nullObjects (N : Set D) (x : D) :
    objectEquiv A D x ∈ nullObjects A D N ↔ x ∈ N := Iff.rfl

/--
概要：半自由な段階分解後に既存 path 商を取った対象型。
方針：具体的な分解と収縮集合の逆像を使う。
規約：元の圏から商への射は増大準同値を挟む屋根で表す。
使われ方：Drinfeld §3.5、KST D4 の導来 dg 商。
-/
abbrev Quotient (N : Set D) := DGQuotient.QuotientObject (Objects A D) (nullObjects A D N)

/--
概要：分解から明示的 path 商への標準 dg 関手。
方針：既存商の包含関手を使う。
規約：元の圏からの厳密な逆 dg 関手は選ばない。
使われ方：Drinfeld §3.5 の dg 商の屋根の右辺。
-/
def projection (N : Set D) : DGFunctor A (Objects A D) (Quotient A D N) :=
  DGQuotient.inclusion A (Objects A D) (nullObjects A D N)

/--
概要：分解後の商の前三角化は、分解後の指定 Verdier 商と同値。
方針：半自由フィルトレーションで証明した片側 K-flat 性を既存定理へ渡す。
規約：冪等完備化を追加しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の局所化の入力。
-/
def quotientTriaEquivalence (N : Set D) :
    TriaQuotient A (Objects A D) (nullObjects A D N) ≌ TriaCategory A (Quotient A D N) :=
  DGQuotient.localQuotientTriaEquivalence A (Objects A D) (nullObjects A D N)
    (localKFlat A D (nullObjects A D N))

/--
概要：分解後の商の前三角化比較の順関手は shift と両立する。
方針：既存の比較関手の shift 構造を保つ。
規約：比較同値と同じ関手を使う。
使われ方：Drinfeld Thm 3.4 の三角比較。
-/
instance quotientTriaEquivalenceFunctorCommShift (N : Set D) :
    (quotientTriaEquivalence A D N).functor.CommShift ℤ :=
  DGQuotient.localQuotientTriaEquivalenceFunctorCommShift A (Objects A D)
    (nullObjects A D N) (localKFlat A D (nullObjects A D N))

/--
概要：分解後の商の前三角化比較の逆関手は shift と両立する。
方針：既存の比較同値の逆関手の構造を保つ。
規約：shift を選び直さない。
使われ方：Drinfeld Thm 3.4 の三角比較。
-/
instance quotientTriaEquivalenceInverseCommShift (N : Set D) :
    (quotientTriaEquivalence A D N).inverse.CommShift ℤ :=
  DGQuotient.localQuotientTriaEquivalenceInverseCommShift A (Objects A D)
    (nullObjects A D N) (localKFlat A D (nullObjects A D N))

/--
概要：分解後の商の前三角化比較は shift と両立する。
方針：既存の比較同値の構造を保持する。
規約：元の圏への移送は別の正方形で比較する。
使われ方：Drinfeld Thm 3.4 の三角比較。
-/
instance quotientTriaEquivalenceCommShift (N : Set D) :
    (quotientTriaEquivalence A D N).CommShift ℤ :=
  DGQuotient.localQuotientTriaEquivalenceCommShift A (Objects A D) (nullObjects A D N)
    (localKFlat A D (nullObjects A D N))

/--
概要：分解後の商の前三角化比較は三角同値。
方針：片側 K-flat 条件を証明して得た既存の三角同値を使う。
規約：未証明の導来比較をフィールドに置かない。
使われ方：Drinfeld Thm 3.4、KST D4 の商の比較。
-/
instance quotientTriaEquivalenceIsTriangulated (N : Set D) :
    (quotientTriaEquivalence A D N).IsTriangulated :=
  DGQuotient.localQuotientTriaEquivalenceIsTriangulated A (Objects A D) (nullObjects A D N)
    (localKFlat A D (nullObjects A D N))

/--
概要：既存の perfect 商比較へ具体的分解の平坦性を供給する。
方針：既存 localPerfectQuotientEquivalence に証明済み localKFlat を渡す。
規約：こちらの比較先は冪等完備化した Verdier 商。
使われ方：Drinfeld Thm 3.4、K-L1b・L3 の完備商への接続。
-/
def perfectQuotientEquivalence (N : Set D) :
    PerfectDGHomotopyCategoryOver A (Quotient A D N) Set.univ ≌
      CompletedTriaQuotient A (Objects A D) (nullObjects A D N) :=
  DGQuotient.localPerfectQuotientEquivalence A (Objects A D) (nullObjects A D N)
    (localKFlat A D (nullObjects A D N))

end SerrePositivity.KST.DerivedGeometry.DGResolution

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Drinfeld "Construction §3.5"] _root_.SerrePositivity.KST.DerivedGeometry.DGResolution.quotientTriaEquivalence

module
public import SerrePositivity.KST.SConstruction.DGGluingDiagonalQuotientPoint
public import SerrePositivity.KST.SConstruction.DGStrictSquareQuotientEnd

/-! # 元の厳密四角形の指定商対象による Perf 生成
概要：元の左関手像と右指定対象の生成条件を、同じ標準対角商へ接続する。
方針：標準対角の左成分を元の左関手と厳密に同定し、実二軸の生成判定を使う。
規約：生成条件は明示入力。使われ方：同じ指定商 End の Morita 比較。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (h : L.comp p = G.comp q) (zc : C)
  (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd)) (b : D)
local notation "I" => dgStrictSquareQuotientInput R C D E p q L G h zc hc b

include hd in
/-- 元の左関手像と右対象が生成すれば、同じ標準対角商の指定対象が Perf を生成する。 -/
lemma dgStrictSquareQuotient_perfectOver_point_eq
    (hL : modulePerfectOver R C (Set.range L.obj) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    modulePerfectOver R (I).quotientObject {(I).projection.obj (I).point} =
      modulePerfect R (I).quotientObject := by
  exact dgGluingDiagonalQuotient_perfectOver_point_eq R C D
    (dgHomGluingBimodule R C D E p q) zc hc zd hd
    (dgStrictSquareDiagonal R C D E p q L G h) b hL hD

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareComparison
public import SerrePositivity.KST.SConstruction.DGHomGluingFunctor

/-! # 元の実 Perf 合成比較を持つ小模型の dg gluing 対角
概要：四辺の実延長を厳密な dg 関手として保持し、元の比較を持つ実対角を構成する。
方針：共通小終域の全 Hom 自然な閉比較を、既存の Hom gluing 関手へ渡す。
規約：比較は元の同型族。使われ方：実 LT 入力の対角像と指定商 End。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q)
local notation "CL" => DGSmallPerfectArrowTarget R P C L
local notation "DR" => DGSmallPerfectArrowTarget R P D G
local notation "V" => DGSmallPerfectSquareCorner R P C D E L G p q
local notation "LS" => dgSmallPerfectArrow R P C L
local notation "GS" => dgSmallPerfectArrow R P D G
local notation "pS" => dgSmallPerfectSquareLeftMap R P C D E L G p q
local notation "qS" => dgSmallPerfectSquareRightMap R P C D E L G p q

/-- 同じ実左右小模型と共通終域から作る、全 Hom を持つ元の dg gluing。 -/
abbrev DGSmallPerfectSquareGluing :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R (CL) (DR) (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS))

/-- 元の実四辺と同じ Perf 合成比較を保持する、実 dg gluing 対角。 -/
def dgSmallPerfectSquareDiagonal :
    DGFunctor R (DGSmallPerfectBase R P) (DGSmallPerfectSquareGluing R P C D E L G p q) :=
  dgHomGluingFunctor R (CL) (DR) (V) (pS) (qS) (LS) (GS)
    (fun x => (dgSmallPerfectSquareComparisonAt R P C D E L G p q h x).hom)
    (dgSmallPerfectSquareComparisonAt_naturality R P C D E L G p q h)

/-- 元の対角の左射影は、同じ元の実延長を持つ左の小模型の射そのもの。 -/
lemma dgSmallPerfectSquareDiagonal_left :
    (dgSmallPerfectSquareDiagonal R P C D E L G p q h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (CL) (DR) (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS))) = (LS) :=
  dgHomGluingFunctor_left R (CL) (DR) (V) (pS) (qS) (LS) (GS)
    (fun x => (dgSmallPerfectSquareComparisonAt R P C D E L G p q h x).hom)
    (dgSmallPerfectSquareComparisonAt_naturality R P C D E L G p q h)

/-- 元の対角の右射影も、同じ元の実延長を持つ右の小模型の射そのもの。 -/
lemma dgSmallPerfectSquareDiagonal_right :
    (dgSmallPerfectSquareDiagonal R P C D E L G p q h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS))) = (GS) :=
  dgHomGluingFunctor_right R (CL) (DR) (V) (pS) (qS) (LS) (GS)
    (fun x => (dgSmallPerfectSquareComparisonAt R P C D E L G p q h x).hom)
    (dgSmallPerfectSquareComparisonAt_naturality R P C D E L G p q h)

end SerrePositivity.KST.SConstruction

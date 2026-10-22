module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareLegs
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionSquareComparison

/-! # 共通小終域内の元の実 Perf 四角形比較
概要：元の三つの実 Perf 合成比較の同型を、同じ実対象を持つ共通小終域へ保つ。
方針：元の比較の閉零射と逆射を全 Hom を保つ充満模型内でそのまま使う。
規約：実延長の合成を厳密等号と仮定しない。使われ方：実 gluing 対角の比較族。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q)
local notation "LS" => dgSmallPerfectArrow R P C L
local notation "GS" => dgSmallPerfectArrow R P D G
local notation "pS" => dgSmallPerfectSquareLeftMap R P C D E L G p q
local notation "qS" => dgSmallPerfectSquareRightMap R P C D E L G p q

/-- 共通小終域内の比較は、元の同じ三つの実 Perf 比較の合成を保持する。 -/
def dgSmallPerfectSquareComparisonAt (x : DGSmallPerfectBase R P) :
    ForgetEnrichment.of (Complex R) ((pS).obj ((LS).obj x)) ≅
      ForgetEnrichment.of (Complex R) ((qS).obj ((GS).obj x)) := by
  let e := perfectDGExtensionSquareAt R P C D E L G p q h x.val
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

/-- 同じ共通小終域内の比較は、元の全 Hom 自然性を保持する。 -/
lemma dgSmallPerfectSquareComparisonAt_naturality (x y : DGSmallPerfectBase R P) :
    ((LS).comp (pS)).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((pS).obj ((LS).obj x)))
      (dgSmallPerfectSquareComparisonAt R P C D E L G p q h y).hom =
    ((GS).comp (qS)).map x y ≫ eHomWhiskerRight (Complex R)
      (dgSmallPerfectSquareComparisonAt R P C D E L G p q h x).hom
      (ForgetEnrichment.of (Complex R) ((qS).obj ((GS).obj y))) :=
  perfectDGExtensionSquareAt_naturality R P C D E L G p q h x.val y.val

end SerrePositivity.KST.SConstruction

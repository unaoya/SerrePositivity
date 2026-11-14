module
public import SerrePositivity.KST.SConstruction.DGOdotTargetCone
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor

/-! # 元の dg 代数四角形の実終域 cone 関手
概要：元の四角形の全 gluing Hom と比較 cone 対象族を同じ実 dg 関手に束ねる。
方針：元の小模型と三比較を持つ Hom 双加群の全 Hom cone 関手を特殊化する。
規約：厳密 dg 入力を保持。使われ方：指定収縮と D β3 の商延長への入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "h" => dgOdotInput_dg_commutes R d
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "LS" => dgSmallPerfectArrow R (A) (C) (L)
local notation "GS" => dgSmallPerfectArrow R (A) (D) (G)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "j" => dgSmallPerfectSquareDiagonal R (A) (C) (D) (E) (L) (G) (p) (q) (h)

/-- 元の四角形の同じ全 Hom と実比較 cone を保持する dg 関手。 -/
def dgOdotTargetFunctor :
    DGFunctor R (DGOdotGluing R d) (PerfectDGModule R (DGOdotCorner R d)) :=
  dgHomGluingConeFunctor R (CL) (DR) (DGOdotCorner R d) (pS) (qS)

/-- 同じ実関手の対象は元の実比較 cone そのもの。 -/
lemma dgOdotTargetFunctor_obj (X : DGOdotGluing R d) :
    (dgOdotTargetFunctor R d).obj X = dgOdotTargetCone R d X := rfl

/-- 同じ実関手の全 Hom 作用は元の三成分を保持する同じ鎖写像。 -/
lemma dgOdotTargetFunctor_map (X Y : DGOdotGluing R d) :
    (dgOdotTargetFunctor R d).map X Y =
      dgHomGluingConeHomMap R (CL) (DR) (DGOdotCorner R d) (pS) (qS) X Y := rfl

end SerrePositivity.KST.SConstruction

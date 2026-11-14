module
public import SerrePositivity.KST.SConstruction.DGOdotTargetCone
public import SerrePositivity.KST.SConstruction.DGHomGluingRightCone

/-! # 元の指定右対象の終域 cone と元の右像の実比較
概要：商 End を定める元の (0,b,0) の cone を、元の右像の代表加群と同定する。
方針：元の左零加群と、その閉零性を同じ標準 cone 同型へ渡す。
規約：元の cone 包含を逆射に保持。使われ方：具体的 ⊙ の比較先 End の同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "I" => dgOdotQuotientInput R d

/-- 元の指定 (0,b,0) の同じ実 cone は、元の右像の実代表加群と同型。 -/
def dgOdotTargetRightConeIso :
    ForgetEnrichment.of (Complex R) (dgOdotTargetCone R d (I).point).val ≅
      ForgetEnrichment.of (Complex R) (representable R ((qS).obj (I).rightPoint)) :=
  dgHomGluingRightConeIso R (DGOdotCorner R d) (CL) (DR) (pS) (qS)
    (dgSmallPerfectArrowTargetZero R (A) (C) (L))
    (dgSmallPerfectArrowTargetZero_isZero R (A) (C) (L)) (I).rightPoint

/-- 同じ実同型の逆射は、元の比較辺の標準 cone 包含そのもの。 -/
lemma dgOdotTargetRightConeIso_inv :
    (dgOdotTargetRightConeIso R d).inv =
      moduleConeInr R (DGOdotCorner R d)
        (dgHomGluingTargetModuleMap R (CL) (DR) (DGOdotCorner R d) (pS) (qS) (I).point) := rfl

/-- 元の標準 cone 包含と同じ比較の合成は、元の右像の恒等射。 -/
lemma dgOdotTargetRightConeIso_inr :
    moduleConeInr R (DGOdotCorner R d)
        (dgHomGluingTargetModuleMap R (CL) (DR) (DGOdotCorner R d) (pS) (qS) (I).point) ≫
      (dgOdotTargetRightConeIso R d).hom = 𝟙 _ :=
  (dgOdotTargetRightConeIso R d).inv_hom_id

end SerrePositivity.KST.SConstruction

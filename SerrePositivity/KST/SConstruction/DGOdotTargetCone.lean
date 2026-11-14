module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetContraction
public import SerrePositivity.KST.SConstruction.DGOdotQuotient

/-! # 元の実 dg 代数四角形の終域 cone と対角像の収縮
概要：同じ実比較対角の元の閉零同型から、実 Perf cone と対象別の収縮元を構成する。
方針：元の共通終域・実三比較を同じ Hom gluing cone の構成へ渡す。
規約：全 Hom 関手は DGOdotTargetFunctor、商延長は DGOdotTargetQuotient に接続。
S 内の自然な零化は主張しない。
使われ方：具体的 ⊙ から元の終域への実比較射の入力。
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

/-- 元の実四辺の像を含む、同じ小さい共通終域。 -/
abbrev DGOdotCorner := DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)

/-- 元の実比較対角の標的である、同じ全 Hom を持つ実 gluing。 -/
abbrev DGOdotGluing := DGSmallPerfectSquareGluing R (A) (C) (D) (E) (L) (G) (p) (q)

/-- 任意の元の gluing 対象の、元の比較辺による同じ終域 Perf cone。 -/
def dgOdotTargetCone (X : DGOdotGluing R d) : PerfectDGModule R (DGOdotCorner R d) :=
  dgHomGluingTargetCone R (CL) (DR) (DGOdotCorner R d) (pS) (qS) X

/-- 同じ実対角像では、元の三つの Perf 比較の閉同型を厳密に回収する。 -/
lemma dgOdotTargetDiagonalMap (x : DGSmallPerfectBase R (A)) :
    dgHomGluingTargetMap R (CL) (DR) (DGOdotCorner R d) (pS) (qS) ((j).obj x) =
      (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E) (L) (G) (p) (q) (h) x).hom :=
  dgHomGluingTargetMap_comparisonObject R (CL) (DR) (DGOdotCorner R d) (pS) (qS) (LS) (GS)
    (fun x => (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E)
      (L) (G) (p) (q) (h) x).hom) x

/-- 元の同じ対角像の Perf cone に指定した、実 End 内の次数 −1 収縮元。 -/
def dgOdotTargetDiagonalContractingElement (x : DGSmallPerfectBase R (A)) :
    GradedHom R (dgOdotTargetCone R d ((j).obj x)) (dgOdotTargetCone R d ((j).obj x)) (-1) :=
  dgHomGluingTargetConeContractingElement R (CL) (DR) (DGOdotCorner R d) (pS) (qS) ((j).obj x)
    (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E) (L) (G) (p) (q) (h) x)
    (dgOdotTargetDiagonalMap R d x)

/-- 同じ指定収縮元の微分は、同じ元の対角像 cone の恒等元。 -/
lemma dgOdotTargetDiagonalContractingElement_d (x : DGSmallPerfectBase R (A)) :
    (homObject R (PerfectDGModule R (DGOdotCorner R d))
      (dgOdotTargetCone R d ((j).obj x)) (dgOdotTargetCone R d ((j).obj x))).d (-1) 0
        (dgOdotTargetDiagonalContractingElement R d x) =
      (unitElement R (dgOdotTargetCone R d ((j).obj x))).val :=
  dgHomGluingTargetConeContractingElement_d R (CL) (DR) (DGOdotCorner R d) (pS) (qS) ((j).obj x)
    (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E) (L) (G) (p) (q) (h) x)
    (dgOdotTargetDiagonalMap R d x)

/-- 同じ元の対角像 cone は、共通終域上の加群ホモトピー圏で零。 -/
lemma dgOdotTargetDiagonalCone_isZero (x : DGSmallPerfectBase R (A)) :
    IsZero ((moduleToHomotopy R (DGOdotCorner R d)).obj
      (ForgetEnrichment.of (Complex R) (dgOdotTargetCone R d ((j).obj x)).val)) :=
  dgHomGluingTargetCone_isZero R (CL) (DR) (DGOdotCorner R d) (pS) (qS) ((j).obj x)
    (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E) (L) (G) (p) (q) (h) x)
    (dgOdotTargetDiagonalMap R d x)

end SerrePositivity.KST.SConstruction

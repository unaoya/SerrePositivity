module
public import SerrePositivity.KST.SConstruction.DGGluingDiagonalQuotientGeneration
public import SerrePositivity.KST.SConstruction.DGGluingRightPointGeneration

/-! # 同じ実対角商の指定右対象による単一生成
概要：左対角成分と右指定対象の生成条件から、元の商の同じ指定対象の生成性を得る。
方針：実二軸三角形と D の対角零化・導来延長の既存 API を合成する。
規約：両生成条件は明示入力。使われ方：同じ商 End の具体的 Morita 比較。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  {A : Type t} [DGCategory R A] (j : DGFunctor R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) (b : D)
local notation "T" => PointedDGQuotientObject R j
local notation "q" => pointedDGQuotientProjection R j
local notation "Q" => moduleToDerived R T
local notation "x" => pointedDGQuotientVertex R j (dgGluingRightAxisObject R C D M zc b)

include hc hd in
/-- 明示した元の二つの生成条件により、同じ商 Perf の包含は指定右対象で判定できる。 -/
lemma dgGluingDiagonalQuotient_perfect_le_of_point
    (hL : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D)
    (P : ObjectProperty (DerivedModuleCategory R T)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts]
    (hb : P ((Q).obj (ForgetEnrichment.of (Complex R) (representable R x)))) :
    modulePerfect R T ≤ P :=
  dgGluingDiagonalQuotient_perfect_le_of_right R C D M zc hc zd hd j hL P
    (dgGluingRightAxis_image_mem_of_point R C D M zc hc T (q) b hD P hb)

include hc hd in
/-- 元の二つの生成条件の下で、同じ実対角商の Perf は指定右対象一つから生成される。 -/
lemma dgGluingDiagonalQuotient_perfectOver_point_eq
    (hL : modulePerfectOver R C (Set.range (fun a => (j.obj a).left)) = modulePerfect R C)
    (hD : modulePerfectOver R D {b} = modulePerfect R D) :
    modulePerfectOver R T {x} = modulePerfect R T := by
  apply le_antisymm
  · exact modulePerfectOver_mono R T (Set.subset_univ _)
  · exact dgGluingDiagonalQuotient_perfect_le_of_point R C D M zc hc zd hd j b hL hD
      (modulePerfectOver R T {x}) (modulePerfectOver_representable R T x (by simp))

end SerrePositivity.KST.SConstruction

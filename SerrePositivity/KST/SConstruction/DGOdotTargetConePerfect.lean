module
public import SerrePositivity.KST.SConstruction.DGOdotTargetConeRepresentationNaturality
public import SerrePositivity.KST.SConstruction.DGPerfectClosedIsoLift

/-! # 元の終域で評価した指定 cone の実 perfect 性
概要：評価した元の cone を同じ実加群のまま射影的 perfect 対象として保持する。
方針：元の自由代表への同型で射影性と導来 perfect 性を移し、元の全 Hom 作用を制限する。
規約：対象・作用を選び直さない。使われ方：元の比較表現の実 Perf 延長への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "gRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (CRaw) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (gRaw)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "Y" => dgSmallPerfectEnvelopeYoneda R (DRaw) (DGSmallPerfectBase R (A))
  (dgSmallPerfectEnvelopeExtensionFamily R (A) (DRaw) Empty
    (dgSmallPerfectBaseFamily R (A)) (gRaw))
local notation "M" => dgHomGluingBimodule R (CL) (DR) (DGOdotCorner R d) (pS) (qS)
local notation "zc" => dgSmallPerfectArrowTargetZero R (A) (CRaw) (L)
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R (A) (CRaw) (L)
local notation "b" => dgOdotInputRightPoint R d

local notation "J" => dgSmallPerfectSquareCornerInclusion R (A) (CRaw) (DRaw) (E)
  (L) (gRaw) (p) (q)

/-- 評価した同じ指定 cone は、元の自由代表との実同型により射影的 perfect。 -/
lemma dgOdotRealizedConePoint_perfect :
    modulePerfectProjectiveOver R (E) Set.univ
      ((dgOdotCornerRealization R d).obj (dgOdotTargetCone R d (I).point).val) := by
  refine ⟨moduleHomotopicallyProjective_of_iso R (E) (dgOdotRealizedConePointIso R d).symm
    (representable_homotopicallyProjective R (E) ((q).obj (b))), ?_⟩
  exact (modulePerfectOver R (E) Set.univ).prop_of_iso
    ((moduleToDerived R (E)).mapIso (dgOdotRealizedConePointIso R d).symm)
    (modulePerfectOver_representable R (E) ((q).obj (b)) (Set.mem_univ _))

/-- 同じ評価済み cone を、その実加群のまま元の終域の Perf に保持する。 -/
def dgOdotRealizedConePerfectPoint : PerfectDGModule R (E) :=
  ⟨(dgOdotCornerRealization R d).obj (dgOdotTargetCone R d (I).point).val,
    dgOdotRealizedConePoint_perfect R d⟩

/-- 指定商 End の同じ評価済み cone 作用を実 Perf へ制限する dg 関手。 -/
def dgOdotRealizedConePerfectRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (PerfectDGModule R (E)) where
  obj _ := dgOdotRealizedConePerfectPoint R d
  map x y := (dgOdotRealizedConeRepresentation R d).map x y
  map_id x := (dgOdotRealizedConeRepresentation R d).map_id x
  map_comp x y z := (dgOdotRealizedConeRepresentation R d).map_comp x y z

/-- 同じ実 Perf 制限の全 Hom 作用を厳密に回収する。 -/
lemma dgOdotRealizedConePerfectRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedConePerfectRepresentation R d).map x y =
      (dgOdotRealizedConeRepresentation R d).map x y := rfl

/-- 同じ実 Perf 制限を加群圏へ含めると、元の同じ評価済み cone 関手を回収する。 -/
lemma dgOdotRealizedConePerfectRepresentation_inclusion :
    (dgOdotRealizedConePerfectRepresentation R d).comp
      (perfectDGModuleInclusion R (E) Set.univ) = dgOdotRealizedConeRepresentation R d := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgOdotRealizedConePerfectRepresentation R d).comp
      (perfectDGModuleInclusion R (E) Set.univ))
    (G := dgOdotRealizedConeRepresentation R d) (fun _ => rfl)
  intro x y
  change (_ ≫ 𝟙 _) ≫ eqToHom (by rfl) = _
  erw [eqToHom_refl, Category.comp_id, Category.comp_id]
  rfl

/-- 同じ自由代表への元の実同型を、同じ実 Perf の閉零同型として保持する。 -/
def dgOdotRealizedConePerfectPointIso :
    ForgetEnrichment.of (Complex R) (dgOdotRealizedConePerfectPoint R d) ≅
      ForgetEnrichment.of (Complex R) (dgRepresentablePerfectPoint R (E) ((q).obj (b))) :=
  dgPerfectClosedIsoLift R (E) (dgOdotRealizedConePerfectPoint R d)
    (dgRepresentablePerfectPoint R (E) ((q).obj (b))) (dgOdotRealizedConePointIso R d)

/-- Perf 内の同じ同型の順射は、包含後に元の三段 cone 同型を回収する。 -/
lemma dgOdotRealizedConePerfectPointIso_hom :
    (perfectDGModuleInclusion R (E) Set.univ).onClosed.map
      (dgOdotRealizedConePerfectPointIso R d).hom = (dgOdotRealizedConePointIso R d).hom :=
  dgPerfectClosedIsoLift_hom R (E) (dgOdotRealizedConePerfectPoint R d)
    (dgRepresentablePerfectPoint R (E) ((q).obj (b))) (dgOdotRealizedConePointIso R d)

/-- Perf 内の同じ同型の逆射も、包含後に元の逆射を回収する。 -/
lemma dgOdotRealizedConePerfectPointIso_inv :
    (perfectDGModuleInclusion R (E) Set.univ).onClosed.map
      (dgOdotRealizedConePerfectPointIso R d).inv = (dgOdotRealizedConePointIso R d).inv :=
  dgPerfectClosedIsoLift_inv R (E) (dgOdotRealizedConePerfectPoint R d)
    (dgRepresentablePerfectPoint R (E) ((q).obj (b))) (dgOdotRealizedConePointIso R d)

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGOdotTargetConePerfect
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeYoneda
public import SerrePositivity.KST.SConstruction.DGFullClosedIsoLift

/-! # 元の評価済み cone 点を保持する小さい実 Perf 模型
概要：同じ cone 点と元の全自由代表を、対象を選び直さず一つの小さい実模型に入れる。
方針：既存の指定像付き Perf envelope を一対象族に適用し、全 Hom 作用を保持する。
規約：全 Perf の Small 性を仮定しない。使われ方：元の比較代数射の実一回 Perf 延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
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

/-- 元の評価済み cone 点そのものを保持する一対象族。 -/
def dgOdotTargetConeFamily : PUnit.{1} → PerfectDGModule R (E) :=
  fun _ => dgOdotRealizedConePerfectPoint R d

/-- 元の cone 点と元の全代表を含む、同じ終域上の小さい実 Perf 模型。 -/
abbrev DGOdotTargetSmallPerfect :=
  DGSmallPerfectEnvelope R (E) PUnit.{1} (dgOdotTargetConeFamily R d)

/-- 全 Perf の小ささを仮定せず、同じ実模型の小ささを得る。 -/
instance dgOdotTargetSmallPerfect_small : Small.{u} (DGOdotTargetSmallPerfect R d) :=
  dgSmallPerfectEnvelopeSmall R (E) PUnit.{1} (dgOdotTargetConeFamily R d)

/-- 元の同じ cone 点を、同じ実模型の指定対象として保持する。 -/
def dgOdotTargetSmallConePoint : DGOdotTargetSmallPerfect R d :=
  dgSmallPerfectEnvelopeOfFamily R (E) PUnit.{1} (dgOdotTargetConeFamily R d) PUnit.unit

/-- 元の終域の指定自由代表を、同じ実模型に保持する。 -/
def dgOdotTargetSmallRepresentablePoint : DGOdotTargetSmallPerfect R d :=
  dgSmallPerfectEnvelopeRepresentable R (E) PUnit.{1} (dgOdotTargetConeFamily R d) ((q).obj (b))

/-- 同じ元の全自由代表と全 Hom を保持する、元の終域からの厳密 Yoneda。 -/
def dgOdotTargetSmallYoneda : DGFunctor R (E) (DGOdotTargetSmallPerfect R d) :=
  dgSmallPerfectEnvelopeYoneda R (E) PUnit.{1} (dgOdotTargetConeFamily R d)

/-- 同じ小模型から元の実 Perf への全 Hom 恒等の包含。 -/
def dgOdotTargetSmallInclusion :
    DGFunctor R (DGOdotTargetSmallPerfect R d) (PerfectDGModule R (E)) :=
  dgSmallPerfectEnvelopeInclusion R (E) PUnit.{1} (dgOdotTargetConeFamily R d)

/-- 指定商 End の元の cone 作用を、同じ実点を含む小模型に保持する。 -/
def dgOdotConeSmallRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d) where
  obj _ := dgOdotTargetSmallConePoint R d
  map x y := (dgOdotRealizedConePerfectRepresentation R d).map x y
  map_id x := (dgOdotRealizedConePerfectRepresentation R d).map_id x
  map_comp x y z := (dgOdotRealizedConePerfectRepresentation R d).map_comp x y z

/-- 元の終域 End 比較の自由代表作用を、同じ実小模型に保持する。 -/
def dgOdotTargetSmallRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d) :=
  ((dgOdotTargetCornerEndMap R d).comp (endomorphismInclusion R ((q).obj (b)))).comp
    (dgOdotTargetSmallYoneda R d)

/-- 小模型の cone 作用を含めると、元の同じ実 Perf 作用を厳密に回収する。 -/
lemma dgOdotConeSmallRepresentation_inclusion :
    (dgOdotConeSmallRepresentation R d).comp (dgOdotTargetSmallInclusion R d) =
      dgOdotRealizedConePerfectRepresentation R d := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgOdotConeSmallRepresentation R d).comp (dgOdotTargetSmallInclusion R d))
    (G := dgOdotRealizedConePerfectRepresentation R d) (fun _ => rfl)
  intro x y
  change (_ ≫ 𝟙 _) ≫ eqToHom (by rfl) = _
  erw [eqToHom_refl, Category.comp_id, Category.comp_id]
  rfl

/-- 元の三段 cone 同型を、同じ小さい実 Perf 模型へ同じ閉射で持ち上げる。 -/
def dgOdotTargetSmallPointIso :
    ForgetEnrichment.of (Complex R) (dgOdotTargetSmallConePoint R d) ≅
      ForgetEnrichment.of (Complex R) (dgOdotTargetSmallRepresentablePoint R d) :=
  dgFullClosedIsoLift R (PerfectDGModule R (E))
    (dgSmallPerfectEnvelopeObjects R (E) PUnit.{1} (dgOdotTargetConeFamily R d))
    (dgOdotTargetSmallConePoint R d) (dgOdotTargetSmallRepresentablePoint R d)
    (dgOdotRealizedConePerfectPointIso R d)

end SerrePositivity.KST.SConstruction

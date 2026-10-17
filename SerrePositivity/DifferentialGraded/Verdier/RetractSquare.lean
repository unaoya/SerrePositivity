module
public import SerrePositivity.DifferentialGraded.Verdier.ComparisonLinear

/-! # 局所商比較の retract 図式と Karoubi の形式的直和因子 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Idempotents

section General
variable {C T : Type*} [Category* C] [Category* T] (F : C ⥤ T) [F.Full] [F.Faithful]
  {X Y : C}

/-- 完全忠実な比較の像の間の retract を、両方の分裂射ごと引き戻す。 -/
def comparisonRetractPreimage (r : Retract (F.obj X) (F.obj Y)) : Retract X Y where
  i := F.preimage r.i
  r := F.preimage r.r
  retract := by
    apply F.map_injective
    rw [CategoryTheory.Functor.map_comp, F.map_preimage, F.map_preimage,
      CategoryTheory.Functor.map_id]
    exact r.retract

lemma comparisonRetract_i_square (r : Retract (F.obj X) (F.obj Y)) :
    F.map (comparisonRetractPreimage F r).i = r.i := F.map_preimage _

lemma comparisonRetract_r_square (r : Retract (F.obj X) (F.obj Y)) :
    F.map (comparisonRetractPreimage F r).r = r.r := F.map_preimage _

lemma comparisonRetract_iff :
    Nonempty (Retract (F.obj X) (F.obj Y)) ↔ Nonempty (Retract X Y) :=
  ⟨fun ⟨r⟩ => ⟨comparisonRetractPreimage F r⟩, fun ⟨r⟩ => ⟨r.map F⟩⟩
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S)

/-- 局所 tria 商比較は retract 関係を保存し反映する。 -/
lemma localTriaRetract_iff (X Y : TriaQuotient A D S) :
    Nonempty (Retract ((localQuotientTriaEquivalence A D S h).functor.obj X)
      ((localQuotientTriaEquivalence A D S h).functor.obj Y)) ↔ Nonempty (Retract X Y) :=
  comparisonRetract_iff (localQuotientTriaEquivalence A D S h).functor

/-- perfect enhancement と完備商の比較も retract 関係を保存し反映する。 -/
lemma localPerfectRetract_iff
    (X Y : PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ) :
    Nonempty (Retract ((localPerfectQuotientEquivalence A D S h).functor.obj X)
      ((localPerfectQuotientEquivalence A D S h).functor.obj Y)) ↔ Nonempty (Retract X Y) :=
  comparisonRetract_iff (localPerfectQuotientEquivalence A D S h).functor

/-- 完備化された比較に沿う、形式的冪等元の分裂の図式。 -/
def localCompletedRetract (P : CompletedTriaQuotient A D S) :=
  (karoubiRetract P).map (localCompletedQuotientEquivalence A D S h).functor

lemma localCompletedRetract_i (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).i.f = (localQuotientTriaFunctor A D S).map P.p := rfl

lemma localCompletedRetract_r (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).r.f = (localQuotientTriaFunctor A D S).map P.p := rfl

lemma localCompletedRetract_split (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).i ≫ (localCompletedRetract A D S h P).r =
      𝟙 ((localCompletedQuotientEquivalence A D S h).functor.obj P) :=
  (localCompletedRetract A D S h P).retract
end DGQuotient
end SerrePositivity.DifferentialGraded

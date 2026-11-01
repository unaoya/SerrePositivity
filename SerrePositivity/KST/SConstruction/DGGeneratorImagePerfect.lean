module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison

/-! # 元の生成代表の H⁰ 比較から実 dg 関手像の Perf 生成へ
概要：元の生成対象と関手像の H⁰ 同型だけから、対象像の Perf 生成条件を供給する。
方針：元の Yoneda と D の既存 K(D)・D(D) 比較を使い、生成代表の導来像を移す。
規約：対象等号や閉零同型は要求しない。使われ方：実 LT 入力の左対角成分の生成。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "Q" => moduleToDerived R D
local notation "K" => moduleToHomotopy R D
local notation "L" => moduleHomotopyToDerivedClosed R D

/-- 元の対象の H⁰ 同型から、同じ二代表の主導来像の同型を得る。 -/
def dgRepresentableDerivedIsoOfHomotopyIso {x y : D}
    (e : (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x) ≅
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) y)) :
    (Q).obj (ForgetEnrichment.of (Complex R) (representable R x)) ≅
      (Q).obj (ForgetEnrichment.of (Complex R) (representable R y)) :=
  ((moduleToHomotopyDerivedIso R D).app
    (ForgetEnrichment.of (Complex R) (representable R x))).symm ≪≫
    (L).mapIso ((dgYoneda R D).onHomotopy.mapIso e) ≪≫
    (moduleToHomotopyDerivedIso R D).app
      (ForgetEnrichment.of (Complex R) (representable R y))

/-- 元の生成対象に H⁰ で同型な対象も、同じ全 Perf を生成する。 -/
lemma dgPerfectOver_singleton_eq_of_generator_iso (b c : D)
    (hgen : modulePerfectOver R D {b} = modulePerfect R D)
    (e : (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) c) ≅
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) b)) :
    modulePerfectOver R D {c} = modulePerfect R D := by
  apply le_antisymm (modulePerfectOver_mono R D (Set.subset_univ _))
  change modulePerfectOver R D {b} = modulePerfectOver R D Set.univ at hgen
  rw [← hgen]
  apply modulePerfectOver_le_of_generators R D (modulePerfectOver R D {c})
  intro y hy
  have hy : y = b := Set.mem_singleton_iff.mp hy
  subst y
  exact (modulePerfectOver R D {c}).prop_of_iso
    (dgRepresentableDerivedIsoOfHomotopyIso R D e)
    (modulePerfectOver_representable R D c (Set.mem_singleton c))

/-- 元の dg 関手像が生成代表を H⁰ 同型まで含めば、その対象像は全 Perf を生成する。 -/
lemma dgPerfectOver_image_eq_of_generator_iso {C : Type w} [DGCategory R C]
    (F : DGFunctor R C D) (a : C) (b : D)
    (hgen : modulePerfectOver R D {b} = modulePerfect R D)
    (e : (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) (F.obj a)) ≅
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) b)) :
    modulePerfectOver R D (Set.range F.obj) = modulePerfect R D := by
  apply le_antisymm (modulePerfectOver_mono R D (Set.subset_univ _))
  change modulePerfectOver R D {b} = modulePerfectOver R D Set.univ at hgen
  rw [← hgen]
  apply modulePerfectOver_le_of_generators R D (modulePerfectOver R D (Set.range F.obj))
  intro y hy
  have hy : y = b := Set.mem_singleton_iff.mp hy
  subst y
  exact (modulePerfectOver R D (Set.range F.obj)).prop_of_iso
    (dgRepresentableDerivedIsoOfHomotopyIso R D e)
    (modulePerfectOver_representable R D (F.obj a) ⟨a, rfl⟩)

end SerrePositivity.KST.SConstruction

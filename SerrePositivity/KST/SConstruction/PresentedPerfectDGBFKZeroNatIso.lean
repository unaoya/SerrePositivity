module
public import SerrePositivity.KST.SConstruction.DGKHomotopyFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFKZero
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroNatIso
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! # 厳密 dg 入力上の Ab 値 K 群と π₀=K₀ の自然同型
概要：同じ実 BF K の整数群を加法記法で束ね、元の Perf 三角圏 K₀ と自然同型にする。
方針：元の厳密 dg 射の安定入力作用を保持し、証明済みの対象類比較の自然性を使う。
規約：一般 dg 圏の H⁰ ではなく同じ Perf の H⁰ を使う。使われ方：L1e・L1f の界面。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
variable (A : Type u) [CommRing A]

/-- 元の同じ実 Perf の安定模型と厳密 dg 入力作用による通常の関手。 -/
def presentedPerfectDGStableModelFunctor : PerfDGInput.{u, v} A ⥤ StableModel.{max (u + 1) v}
    where
  obj X := stableCategoryModel (presentedPerfectDGStableCategory A X)
  map f := presentedPerfectDGBFInputStableMap A f
  map_id X := Subtype.ext ((presentedPerfectDGQCatFunctor A).map_id X)
  map_comp f g := Subtype.ext ((presentedPerfectDGQCatFunctor A).map_comp f g)

/-- 元の実 BF K の整数群を、加法記法の Ab 値関手として保持する。 -/
def presentedPerfectDGBFAdditiveHomotopyFunctor (j : ℤ) :
    PerfDGInput.{u, v} A ⥤ AddCommGrpCat.{max (u + 1) v} :=
  presentedPerfectDGBFHomotopyFunctor A j ⋙ CommGrpCat.toAddCommGrp

/-- 元の dgKMap の同じ整数 π 作用を、加法記法の Ab 値関手として保持する。 -/
def dgKAdditiveHomotopyFunctor (j : ℤ) :
    PerfDGInput.{u, v} A ⥤ AddCommGrpCat.{max (u + 1) v} :=
  dgKHomotopyFunctor A j ⋙ CommGrpCat.toAddCommGrp

/-- 同じ実 BF 比較射による元の dgK 群との比較は、Ab 値でも自然同型。 -/
def presentedPerfectDGBFDGKAdditiveNatIso (j : ℤ) :
    presentedPerfectDGBFAdditiveHomotopyFunctor A j ≅ dgKAdditiveHomotopyFunctor A j :=
  Functor.isoWhiskerRight (presentedPerfectDGBFDGKHomotopyNatIso A j) CommGrpCat.toAddCommGrp

/-- 同じ Perf の三角圏 K₀ と、同じ実 BF K の零次 Ab 値関手との自然同型。 -/
def presentedPerfectDGBFKZeroNatIso :
    presentedPerfectDGStableModelFunctor A ⋙ triangulatedKZeroFunctor ≅
      presentedPerfectDGBFAdditiveHomotopyFunctor A 0 :=
  NatIso.ofComponents (fun X => (presentedPerfectDGBFKZeroEquiv A X).toAddCommGrpIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro a
    exact presentedPerfectDGBFKZeroEquiv_naturality A f a)

end SerrePositivity.KST.SConstruction

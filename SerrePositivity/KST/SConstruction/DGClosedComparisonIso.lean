module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedNaturality

/-! # 全 Hom 比較の閉零自然同型
概要：全次数で自然な閉零同型族を、同じ成分の通常の自然同型に束ねる。
方針：抽象 dg 関手で閉零自然性を先に検証し、具体的延長に適用する。
規約：元の同型族を変更しない。使われ方：ラベル付き Perf の評価比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] (F G : DGFunctor A D E)

/-- 全 Hom 自然な閉零同型族から、同じ成分の閉零自然同型を構成する。 -/
def dgFunctorClosedComparisonIso
    (e : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ≅
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom =
      G.map x y ≫ eHomWhiskerRight (Complex A) (e x).hom
        (ForgetEnrichment.of (Complex A) (G.obj y))) : F.onClosed ≅ G.onClosed :=
  NatIso.ofComponents (fun X => e (ForgetEnrichment.to (Complex A) X))
    (fun f => dgFunctorClosedComparison_naturality A F G (fun x => (e x).hom) h f)

end SerrePositivity.KST.SConstruction

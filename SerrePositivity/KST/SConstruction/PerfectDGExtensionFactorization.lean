module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionSquareComparison

/-! # 元の厳密 dg 因子分解の実 Perf 延長比較
概要：元の厳密因子分解を、同じ合成比較と入力等号移送を通る実 Perf 同型へ移す。
方針：元の二比較を合成し、全 Hom 自然性を同じ射について保持する。
規約：元の Perf 延長を変更しない。使われ方：標準対角の両 Perf 射影。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R P C) (G : DGFunctor R C D) (H : DGFunctor R P D) (h : F.comp G = H)

/-- 元の厳密因子分解を通る、同じ二回延長と一回延長の指定同型。 -/
def perfectDGExtensionFactorizationAt (X : PerfectDGModule R P) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R P C F).comp (perfectDGExtension R C D G)).obj X) ≅
    ForgetEnrichment.of (Complex R) ((perfectDGExtension R P D H).obj X) :=
  (perfectDGExtensionCompositionAt R P C D F G X) ≪≫
    (perfectDGExtensionInputIso R P D h X)

/-- 同じ因子分解の指定比較は、全 Hom 複体上で自然。 -/
lemma perfectDGExtensionFactorizationAt_naturality (X Y : PerfectDGModule R P) :
    ((perfectDGExtension R P C F).comp (perfectDGExtension R C D G)).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGExtension R P C F).comp (perfectDGExtension R C D G)).obj X))
        (perfectDGExtensionFactorizationAt R P C D F G H h Y).hom =
    (perfectDGExtension R P D H).map X Y ≫ eHomWhiskerRight (Complex R)
      (perfectDGExtensionFactorizationAt R P C D F G H h X).hom
      (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P D H).obj Y)) :=
  dgClosedComparison_comp (Complex R)
    (perfectDGExtensionCompositionAt R P C D F G X).hom
    (perfectDGExtensionCompositionAt R P C D F G Y).hom
    (perfectDGExtensionInputIso R P D h X).hom (perfectDGExtensionInputIso R P D h Y).hom
    _ _ _ (perfectDGExtensionCompositionAt_naturality R P C D F G X Y)
    (perfectDGExtensionInputIso_naturality R P D h X Y)

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGClosedComparisonComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingStrictSquare
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionTriangle

/-! # 元の厳密 dg 四角形の実 Perf 延長比較
概要：四角形の二つの実 Perf 延長の合成を、元の合成比較と入力等号で比較する。
方針：元の閉零同型三つを貼り、全 Hom 自然性を同じ比較射について証明する。
規約：実 Perf の Small 性を要求しない。使われ方：標準対角の Perf 比較データ。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の入力等号からの実 Perf 延長の閉比較は、全 Hom 上で自然。 -/
lemma perfectDGExtensionInputIso_naturality
    (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
    (E : Type w) [DGCategory R E] [Small.{u} E]
    {F G : DGFunctor R P E} (h : F = G) (X Y : PerfectDGModule R P) :
    (perfectDGExtension R P E F).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P E F).obj X))
        (perfectDGExtensionInputIso R P E h Y).hom =
    (perfectDGExtension R P E G).map X Y ≫
      eHomWhiskerRight (Complex R) (perfectDGExtensionInputIso R P E h X).hom
        (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P E G).obj Y)) := by
  exact dgFunctorEq_closed_naturality (perfectDGExtension R P E F)
    (perfectDGExtension R P E G)
    (congrArg (fun H : DGFunctor R P E => perfectDGExtension R P E H) h) X Y

variable (R : Type u) [CommRing R] (P : Type v) [DGCategory R P] [Small.{u} P]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (L : DGFunctor R P C) (G : DGFunctor R P D)
  (p : DGFunctor R C E) (q : DGFunctor R D E) (h : L.comp p = G.comp q)

/-- 元の左の二回延長から、元の右合成入力の一回延長への指定比較。 -/
def perfectDGExtensionSquareViaInputAt (X : PerfectDGModule R P) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).obj X) ≅
    ForgetEnrichment.of (Complex R) ((perfectDGExtension R P E (G.comp q)).obj X) :=
  (perfectDGExtensionCompositionAt R P C E L p X) ≪≫
    (perfectDGExtensionInputIso R P E h X)

omit [Small.{u} D] in
/-- 同じ二つの元の比較を合成した射は、全 Hom 上で自然。 -/
lemma perfectDGExtensionSquareViaInputAt_naturality (X Y : PerfectDGModule R P) :
    ((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).obj X))
        (perfectDGExtensionSquareViaInputAt R P C D E L G p q h Y).hom =
    (perfectDGExtension R P E (G.comp q)).map X Y ≫
      eHomWhiskerRight (Complex R)
        (perfectDGExtensionSquareViaInputAt R P C D E L G p q h X).hom
        (ForgetEnrichment.of (Complex R) ((perfectDGExtension R P E (G.comp q)).obj Y)) :=
  dgClosedComparison_comp (Complex R)
    (perfectDGExtensionCompositionAt R P C E L p X).hom
    (perfectDGExtensionCompositionAt R P C E L p Y).hom
    (perfectDGExtensionInputIso R P E h X).hom (perfectDGExtensionInputIso R P E h Y).hom
    _ _ _ (perfectDGExtensionCompositionAt_naturality R P C E L p X Y)
    (perfectDGExtensionInputIso_naturality R P E h X Y)

/-- 元の四角形の二つの実 Perf 延長を結ぶ、同じ三つの比較の合成。 -/
def perfectDGExtensionSquareAt (X : PerfectDGModule R P) :
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).obj X) ≅
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R P D G).comp (perfectDGExtension R D E q)).obj X) :=
  (perfectDGExtensionSquareViaInputAt R P C D E L G p q h X) ≪≫
    (perfectDGExtensionCompositionAt R P D E G q X).symm

/-- 同じ三つの元の比較を通る実四角形比較は、全 Hom 上で自然。 -/
lemma perfectDGExtensionSquareAt_naturality (X Y : PerfectDGModule R P) :
    ((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          (((perfectDGExtension R P C L).comp (perfectDGExtension R C E p)).obj X))
        (perfectDGExtensionSquareAt R P C D E L G p q h Y).hom =
    ((perfectDGExtension R P D G).comp (perfectDGExtension R D E q)).map X Y ≫
      eHomWhiskerRight (Complex R)
        (perfectDGExtensionSquareAt R P C D E L G p q h X).hom
        (ForgetEnrichment.of (Complex R)
          (((perfectDGExtension R P D G).comp (perfectDGExtension R D E q)).obj Y)) :=
  dgClosedComparison_comp (Complex R)
    (perfectDGExtensionSquareViaInputAt R P C D E L G p q h X).hom
    (perfectDGExtensionSquareViaInputAt R P C D E L G p q h Y).hom
    (perfectDGExtensionCompositionAt R P D E G q X).inv
    (perfectDGExtensionCompositionAt R P D E G q Y).inv _ _ _
    (perfectDGExtensionSquareViaInputAt_naturality R P C D E L G p q h X Y)
    (dgFunctorClosedComparison_inv_naturality R _ _
      (perfectDGExtensionCompositionAt R P D E G q)
      (perfectDGExtensionCompositionAt_naturality R P D E G q) X Y)

end SerrePositivity.KST.SConstruction

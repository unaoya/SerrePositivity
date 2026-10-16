module
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-! # 値ごとのquasiIsoの標準局所化による導来bimodule圏

全Hom自然な閉零bimodule射を局所化する。局所化の標準の大きい射宇宙を保持し、
小さいHomや射影モデル構造の存在はこの定義の前提にしない。
-/
@[expose] public section
noncomputable section
universe u v w z z'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 指定した値ごとの準同型を局所化した導来bimodule圏。 -/
abbrev DerivedBimoduleCategory := (BimoduleCategory.quasiIso A B C).Localization

/-- 元の全dg自然な閉零bimodule圏からの指定局所化関手。 -/
abbrev bimoduleToDerived : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B C :=
  (BimoduleCategory.quasiIso A B C).Q

lemma bimoduleToDerived_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (bimoduleToDerived A B C) :=
  Localization.inverts _ _

def bimoduleDerivedIso {M N : BimoduleCategory A B C} (f : M ⟶ N)
    (hf : BimoduleCategory.quasiIso A B C f) :
    (bimoduleToDerived A B C).obj M ≅ (bimoduleToDerived A B C).obj N :=
  Localization.Construction.wIso (W := BimoduleCategory.quasiIso A B C) f hf

variable {T : Type z} [Category.{z'} T]

/-- 指定準同型を反転する関手の、標準局所化への延長。 -/
def bimoduleDerivedLift (G : BimoduleCategory A B C ⥤ T)
    (hG : (BimoduleCategory.quasiIso A B C).IsInvertedBy G) :
    DerivedBimoduleCategory A B C ⥤ T := Localization.Construction.lift G hG

lemma bimoduleDerivedLift_fac (G : BimoduleCategory A B C ⥤ T)
    (hG : (BimoduleCategory.quasiIso A B C).IsInvertedBy G) :
    bimoduleToDerived A B C ⋙ bimoduleDerivedLift A B C G hG = G :=
  Localization.Construction.fac G hG

lemma bimoduleDerivedLift_unique (G H : DerivedBimoduleCategory A B C ⥤ T)
    (h : bimoduleToDerived A B C ⋙ G = bimoduleToDerived A B C ⋙ H) : G = H :=
  Localization.Construction.uniq G H h

lemma bimoduleDerivedNatTrans_ext {G H : DerivedBimoduleCategory A B C ⥤ T} {a b : G ⟶ H}
    (h : ∀ M, a.app ((bimoduleToDerived A B C).obj M) =
      b.app ((bimoduleToDerived A B C).obj M)) : a = b :=
  Localization.natTrans_ext (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C) h

end SerrePositivity.DifferentialGraded

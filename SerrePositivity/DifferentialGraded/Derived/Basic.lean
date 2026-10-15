module
public import SerrePositivity.DifferentialGraded.Module.HomotopyQuasiIso
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-! # objectwise quasiIso の局所化による導来加群圏

Mathlib の構成された局所化を使用する。対象宇宙は max (u+1) v、
射宇宙も max (u+1) v。この段階ではより小さい射宇宙を主張しない。
閉零圏と K(D) の両方の局所化を定義し、比較は後続の cylinder 証明で行う。
-/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 dg 自然な閉零射の objectwise quasiIso による構成された局所化 D(D)。 -/
abbrev DerivedModuleCategory := (moduleQuasiIso A D).Localization

/-- 閉零加群圏から D(D) への指定局所化関手。 -/
abbrev moduleToDerived : ModuleCategory A D ⥤ DerivedModuleCategory A D :=
  (moduleQuasiIso A D).Q

/-- 比較対象：K(D) を同じ objectwise quasiIso で局所化する。 -/
abbrev HomotopyDerivedModuleCategory := (moduleHomotopyQuasiIso A D).Localization

/-- K(D) からその quasiIso 局所化への指定関手。 -/
abbrev moduleHomotopyToDerived : ModuleHomotopyCategory A D ⥤
    HomotopyDerivedModuleCategory A D := (moduleHomotopyQuasiIso A D).Q

/-- 標準射宇宙における HasLocalization の具体的データ。小さい射宇宙の選択を強制しない。 -/
@[instance_reducible]
def moduleStandardLocalization : (moduleQuasiIso A D).HasLocalization.{max (u + 1) v} :=
  MorphismProperty.HasLocalization.standard _

lemma moduleToDerived_inverts : (moduleQuasiIso A D).IsInvertedBy (moduleToDerived A D) :=
  Localization.inverts _ _

lemma moduleHomotopyToDerived_inverts :
    (moduleHomotopyQuasiIso A D).IsInvertedBy (moduleHomotopyToDerived A D) :=
  Localization.inverts _ _

/-- 指定準同型の像の同型。 -/
def moduleDerivedIso {M N : ModuleCategory A D} (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    (moduleToDerived A D).obj M ≅ (moduleToDerived A D).obj N :=
  Localization.Construction.wIso (W := moduleQuasiIso A D) f hf

variable {E : Type w} [Category.{w'} E]

/-- 指定射を反転する任意の関手の厳密な延長。対象圏の宇宙は独立。 -/
def moduleDerivedLift (F : ModuleCategory A D ⥤ E)
    (hF : (moduleQuasiIso A D).IsInvertedBy F) : DerivedModuleCategory A D ⥤ E :=
  Localization.Construction.lift F hF

lemma moduleDerivedLift_fac (F : ModuleCategory A D ⥤ E)
    (hF : (moduleQuasiIso A D).IsInvertedBy F) :
    moduleToDerived A D ⋙ moduleDerivedLift A D F hF = F :=
  Localization.Construction.fac F hF

lemma moduleDerivedLift_unique (F G : DerivedModuleCategory A D ⥤ E)
    (h : moduleToDerived A D ⋙ F = moduleToDerived A D ⋙ G) : F = G :=
  Localization.Construction.uniq F G h

/-- 自然変換も局所化前の対象上の成分で判定できる。 -/
lemma moduleDerivedNatTrans_ext {F G : DerivedModuleCategory A D ⥤ E} {α β : F ⟶ G}
    (h : ∀ M : ModuleCategory A D,
      α.app ((moduleToDerived A D).obj M) = β.app ((moduleToDerived A D).obj M)) : α = β :=
  Localization.natTrans_ext (moduleToDerived A D) (moduleQuasiIso A D) h

/-- 関手と自然変換を含む局所化の普遍性。 -/
def moduleDerivedUniversalEquivalence (E : Type w) [Category.{w'} E] :
    (DerivedModuleCategory A D ⥤ E) ≌ (moduleQuasiIso A D).FunctorsInverting E :=
  Localization.functorEquivalence (moduleToDerived A D) (moduleQuasiIso A D) E

end SerrePositivity.DifferentialGraded

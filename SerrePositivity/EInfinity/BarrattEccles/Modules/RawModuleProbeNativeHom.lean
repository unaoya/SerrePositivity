module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeDoldKanHom
public import SerrePositivity.EInfinity.ComplexLimits.DoldKanPinchedChainNaturality

/-!
# 元の半自由 probe の実 pinched Hom への端点同定

概要：M10 の同じ dg Hom 端点を指定半自由模型の実 pinched Hom へ同定する。
方針：既存の実 Dold–Kan/pinched 同型と同じ Hom 鎖写像への自然性を適用する。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、元の指定模型を保持する。
使われ方：同じ局所化比較 K の誘導射と具体的な frame Hom の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]

/-- 概要：同じ二つの元の半自由 probe の実 Dold–Kan は指定模型の実 pinched Hom。
方針：充満 dg 部分圏の同じ Hom に既存の同型を適用する。
規約：HA 1.3.1.13、全単体。使われ方：K の Hom 射の指定端点。 -/
def strictRawModuleProbeNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) :=
  doldKanHomPinchedIso (R := A)
    (D := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
    (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

/-- 概要：同じ全単体テンソル Hom は指定半自由模型の実 pinched Hom と同型。
方針：同じ二変数 Dold–Kan 同型を持ち上げ、同じ端点同型を合成する。
規約：HA 1.3.1.13、元の二つの probe。使われ方：実モデルの frame Hom の端点。 -/
def strictRawModuleProbeTensorNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeTensorHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) :=
  SSet.uliftFunctor.{u + 1, u}.mapIso
    (((strictRawModuleProbeTensorDoldKanIso A X).app (op P)).app
      ((strictRawModuleProbeFunctor A X).obj Q)) ≪≫ strictRawModuleProbeNativeHomIso A X P Q

/-- 概要：同じ端点同型は任意の元の Hom 鎖写像による作用と可換。
方針：既存の実 Dold–Kan/pinched 同型の鎖写像自然性を使う。
規約：HA 1.3.1.13、同じ全単体の作用。使われ方：K の射と比較する Hom 作用の固定。 -/
lemma strictRawModuleProbeNativeHomIso_chainMap (X : (operad A).Algebra)
    (P Q P' Q' : strictRawModuleProbeCategory A X)
    (φ : homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) ⟶
        homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
          (ForgetEnrichment.to (Complex A) P') (ForgetEnrichment.to (Complex A) Q')) :
    SSet.uliftFunctor.{u + 1, u}.map (doldKanHomSpaceChainMap
      (D := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (E := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) Q)
      (x' := ForgetEnrichment.to (Complex A) P') (y' := ForgetEnrichment.to (Complex A) Q') φ) ≫
        (strictRawModuleProbeNativeHomIso A X P' Q').hom =
      (strictRawModuleProbeNativeHomIso A X P Q).hom ≫ pinchedHomChainMap φ :=
  doldKanHomPinchedIso_chainMap φ

end SerrePositivity.EInfinity.BarrattEccles

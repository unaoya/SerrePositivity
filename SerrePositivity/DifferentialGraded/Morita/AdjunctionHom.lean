module
public import SerrePositivity.DifferentialGraded.Morita.KernelTensor
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHom

/-! # 任意kernelの通常Hom dg関手

## 概要
右E・左D kernel Pに対し、Hom_E(P(d),N)を値とする右D加群を全Hom自然に構成する。

## 方針
大きい加群dg圏上の代表加群をPに沿って制限し、パラメータ付きYoneda作用を引き戻す。

## 規約と注意
全右E加群型のSmallは仮定しない。Homの局所K-flat性・kernelの射影性も不要。
これは通常Homであり、一般の導来右随伴の構成とは区別する。

## 使われ方
U16aの一般kernelのtensor–Hom随伴と右導来化の基礎。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- kernelに沿って大きい加群dg圏の代表加群を制限する。 -/
def kernelHomModule (N : RightModule A E) : RightModule A D :=
  restrictModule A D (RightModule A E) P.toFunctor.op (representable A N)

/-- 通常Homの後合成を、全Hom自然なパラメータ付き族として定義する。 -/
def kernelHomParam (M N : RightModule A E) :
    ModuleParamTrans A D (moduleHom A E M N)
      (kernelHomModule A D E P M) (kernelHomModule A D E P N) :=
  moduleRestrictionParam A D (RightModule A E) P.toFunctor.op
    (yonedaExtension A M (representable A N) (𝟙 _))

/-- 任意kernelの通常Hom dg関手。大きい全加群型のSmallは不要。 -/
def kernelHom : DGFunctor A (RightModule A E) (RightModule A D) :=
  (Bimodule.ofParamTrans A D (RightModule A E) (kernelHomModule A D E P)
    (kernelHomParam A D E P)
    (by
      intro N d
      change eId (Complex A) N ≫
        yonedaExtensionApp A N (representable A N) (𝟙 _) (op (P.rightAt d.unop)) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable A (P.rightAt d.unop)).map_id N)
    (by
      intro M N T d
      change eComp (Complex A) M N T ≫
        yonedaExtensionApp A M (representable A T) (𝟙 _) (op (P.rightAt d.unop)) =
        (yonedaExtensionApp A M (representable A N) (𝟙 _) (op (P.rightAt d.unop)) ⊗ₘ
          yonedaExtensionApp A N (representable A T) (𝟙 _) (op (P.rightAt d.unop))) ≫
          enrichedComposition _ _ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable A (P.rightAt d.unop)).map_comp M N T)).toFunctor

/-- 通常Hom関手の値は元の全Hom endそのもの。 -/
lemma kernelHom_value (N : RightModule A E) (d : D) :
    ((kernelHom A D E P).obj N).obj (op d) = moduleHom A E (P.rightAt d) N := rfl

/-- 通常Hom関手の全Hom mapは、各列からの共変representableのmapに一致する。 -/
lemma kernelHom_map_π (M N : RightModule A E) (d : D) :
    (kernelHom A D E P).map M N ≫
        moduleHomπ A D ((kernelHom A D E P).obj M) ((kernelHom A D E P).obj N) d =
      (leftRepresentable A (P.rightAt d)).map M N := by
  change (moduleHomEquiv A D _ _ _).symm (kernelHomParam A D E P M N) ≫
    moduleHomπ A D (kernelHomModule A D E P M) (kernelHomModule A D E P N) d = _
  rw [moduleHomEquiv_symm_π]
  exact endomorphismYonedaApp A (RightModule A E) (P.rightAt d) M N

/-- 通常Homの閉零射の評価は、元の全Hom endの後合成射。 -/
lemma kernelHom_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map ((kernelHom A D E P).onClosed.map f) =
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (P.rightAt d)) f := by
  let M₀ := ForgetEnrichment.to (Complex A) M
  let N₀ := ForgetEnrichment.to (Complex A) N
  calc
    _ = (moduleEvaluation A (EndomorphismObject (P.rightAt d)) .point).map
        ((endomorphismModuleHom A E (P.rightAt d)).onClosed.map f) := by
      apply Cochain.ofHom_injective
      rw [moduleEvaluation_cochain, moduleEvaluation_cochain]
      change (moduleHomπ A D _ _ d).f 0
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
            (kernelHom A D E P).map M₀ N₀)).val =
        (moduleHomπ A (EndomorphismObject (P.rightAt d)) _ _ .point).f 0
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
            (endomorphismModuleHom A E (P.rightAt d)).map M₀ N₀)).val
      rw [cycleFromUnit_postcomp, cycleFromUnit_postcomp]
      have h := (kernelHom_map_π A D E P M₀ N₀ d).trans
        (endomorphismModuleHom_map_π A E (P.rightAt d) M₀ N₀).symm
      exact congrArg (fun k => k.f 0 (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) f)).val) h
    _ = _ := endomorphismModuleHom_map_eval A E (P.rightAt d) M₀ N₀ f .point

end SerrePositivity.DifferentialGraded.Morita

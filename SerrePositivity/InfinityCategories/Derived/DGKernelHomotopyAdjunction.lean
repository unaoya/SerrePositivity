module
public import SerrePositivity.InfinityCategories.Derived.DGKernelInfinityClassicalComparison
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionDerived
/-!
概要：同じ kernel ∞ 関手の通常の h に、既存 telescope の実右随伴を移送する。
方針：主導来圏との比較同値と同じ kernel 作用の全関手自然同型を使う。
規約：ここでは通常の h 上の随伴のみ。使われ方：実余単位の代表と全 Hom 検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 通常の h と主導来加群圏の比較同値。 -/
def dgModuleDerivedHomotopyEquivalence :
    hoFunctor.obj (dgModuleDerivedInfinityCategory R D) ≌ DerivedModuleCategory R D :=
  (dgStableHomotopyEquivalence R (SemifreeDGModules R D)).trans
    (dgSemifreeModuleToDerived R D).asEquivalence

/-- 同じ telescope の右随伴を通常の h 上へ戻す。 -/
def dgKernelHomotopyRightAdjoint (P : Bimodule R E D) :
    hoFunctor.obj (dgModuleDerivedInfinityCategory R E) ⥤
      hoFunctor.obj (dgModuleDerivedInfinityCategory R D) :=
  (dgModuleDerivedHomotopyEquivalence R E).functor ⋙
    Morita.kernelDerivedHom R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)) ⋙
    (dgModuleDerivedHomotopyEquivalence R D).inverse

/-- 元の kernel ∞ 関手の通常の h 上の随伴。 -/
def dgKernelHomotopyAdjunction (P : Bimodule R E D) :
    (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor ⊣
      dgKernelHomotopyRightAdjoint R D E P := by
  let HD := dgModuleDerivedHomotopyEquivalence R D
  let HE := dgModuleDerivedHomotopyEquivalence R E
  let K := (bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)
  let T := Morita.kernelDerivedTensor R D E K
  have eT : T ≅ Morita.kernelDerivedTensorOnBimodule R D E P :=
    Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P)
  have e : (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor ⋙ HE.functor ≅
      HD.functor ⋙ T :=
    (Functor.associator _ _ _).trans (dgKernelDerivedInfinity_classicalIso R D E P) ≪≫
      Functor.associator _ _ _ |>.trans (Functor.isoWhiskerLeft HD.functor eT.symm)
  have e' : (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor ≅
      (HD.functor ⋙ T) ⋙ HE.inverse := CategoryTheory.Iso.isoCompInverse e
  exact ((HD.toAdjunction.comp (Morita.kernelDerivedAdjunction R D E K)).comp
    HE.symm.toAdjunction).ofNatIsoLeft e'.symm
end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelInfinityClassicalComparison
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 通常の h と主導来加群圏の比較同値。 -/
def dgModuleDerivedHomotopyEquivalence :
    hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ≌ DerivedModuleCategory R D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D).asEquivalence

/-- 同じ telescope の右随伴を通常の h 上へ戻す。 -/
def dgKernelHomotopyRightAdjoint (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E) ⥤
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :=
  (dgModuleDerivedHomotopyEquivalence R E).functor ⋙
    _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedHom R D E
      ((_root_.SerrePositivity.DifferentialGraded.bimoduleToDerived R E D).obj (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)) ⋙
    (dgModuleDerivedHomotopyEquivalence R D).inverse

/-- 元の kernel ∞ 関手の通常の h 上の随伴。 -/
def dgKernelHomotopyAdjunction (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor ⊣
      dgKernelHomotopyRightAdjoint R D E P := by
  let HD := dgModuleDerivedHomotopyEquivalence R D
  let HE := dgModuleDerivedHomotopyEquivalence R E
  let K := (_root_.SerrePositivity.DifferentialGraded.bimoduleToDerived R E D).obj (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)
  let T := _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensor R D E K
  have eT : T ≅ Morita.kernelDerivedTensorOnBimodule R D E P :=
    _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimoduleIso R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)
  have e : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor ⋙ HE.functor ≅
      HD.functor ⋙ T :=
    (Functor.associator _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_classicalIso R D E P) ≪≫
      Functor.associator _ _ _ |>.trans (Functor.isoWhiskerLeft HD.functor eT.symm)
  have e' : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor ≅
      (HD.functor ⋙ T) ⋙ HE.inverse := CategoryTheory.Iso.isoCompInverse e
  exact ((HD.toAdjunction.comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedAdjunction R D E K)).comp
    HE.symm.toAdjunction).ofNatIsoLeft e'.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories

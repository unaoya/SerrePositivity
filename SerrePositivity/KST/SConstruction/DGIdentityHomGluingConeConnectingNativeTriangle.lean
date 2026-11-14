module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNatTransNerveHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-!
概要：元 cone 入力・実 connecting・元 connecting の指定三辺を持つ実二単体を保持する。
方針：元全厳密合成等号を既存の native 合成則と指定三辺の三角形存在定理へ渡す。
規約：同じ三つの全ホモトピーを境界として保持する。
使われ方：逆 shift・全実逆回転を含む指定境界比較の connecting 面。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories SSet
/-- 概要：全厳密合成等号から指定三辺の実合成二単体を得る。
方針：native 合成則を指定三辺の既存延長へ渡す。
規約：三つの全ホモトピーを保持。使われ方：実 connecting の指定比較面。 -/
lemma dgModuleStrictCompositionTriangle_nonempty {R : Type u} [CommRing R] {C : Type v}
    [DGCategory R C] [Small.{u} C] {P : Type (max (u + 1) v)} [DGCategory R P]
    (F G H : DGFunctor R P (RightModule R C))
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) (ξ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F H)
    (hξ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ = ξ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle η.homotopy θ.homotopy ξ.homotopy) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq
    η.homotopy θ.homotopy ξ.homotopy
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopyHom_comp R P (RightModule R C) η θ).symm.trans
      (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F H =>
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t.homotopy)) hξ))
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (J)) (moduleShiftDG R C 1)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)

/-- 概要：同じ元三辺の全ホモトピーを境界とする connecting の実合成二単体。
方針：全厳密合成等号を既存の指定三辺の実三角形へ接続する。
規約：三境界を辺の類だけに弱めない。
使われ方：元実逆回転を含む指定合成面の connecting 境界。 -/
def dgIdentityHomGluingConeConnectingNativeTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (dgIdentityHomGluingStrictConeInputComparison R C F G a h).homotopy
      (dgIdentityHomGluingConeConnectingComparison R C F G a h).homotopy (δ).homotopy := by
  exact Classical.choice (dgModuleStrictCompositionTriangle_nonempty (R := R) (C := C) (A) (B) (FS)
    (dgIdentityHomGluingStrictConeInputComparison R C F G a h)
    (dgIdentityHomGluingConeConnectingComparison R C F G a h) (δ)
    (dgIdentityHomGluingConeConnectingComparison_input R C F G a h))
end SerrePositivity.KST.SConstruction

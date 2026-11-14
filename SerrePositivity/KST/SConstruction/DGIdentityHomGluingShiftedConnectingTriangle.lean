module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingShiftedConnecting
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingNativeTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGStrictNatTransHomotopyWhisker
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorTrianglePostcomposition

/-!
概要：元 connecting の同じ実二単体を逆 shift し指定三辺を保持する。
方針：既存の全二単体の後合成を同じ native dg shift へ適用する。
規約：新しい二単体を選び直さない。
使われ方：元実逆回転後の指定上二単体の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories SSet MonoidalClosed
open scoped Simplicial
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
local notation "S" => moduleShiftDG R C (-1)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "α" => dgIdentityHomGluingStrictConeInputComparison R C F G a h
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "αs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (α) (S)
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)
local notation "δs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)


local notation "T" => dgIdentityHomGluingConeConnectingNativeTriangle R C F G a h

/-- 概要：元 connecting 二単体そのものの逆 shift 像。
方針：同じ図式を内部 Hom の native shift で後合成。
規約：三辺を選び直さない。使われ方：元実逆回転の指定合成面。 -/
def dgIdentityHomGluingShiftedConnectingTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (α).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (S)))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (β).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (S)))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (δ).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (S))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.postcomposeFunctorCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (S)) (T)
local notation "TS" => dgIdentityHomGluingShiftedConnectingTriangle R C F G a h

/-- 概要：逆 shift 二単体の全図式は元二単体の指定後合成。
方針：同じ既存構成子の図式定義を回収する。
規約：二単体全体の等号。使われ方：指定面を保つ長方形比較。 -/
lemma dgIdentityHomGluingShiftedConnectingTriangle_diagram :
    (TS).diagram = (T).diagram ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (S)) := rfl

/-- 概要：元後辺の逆 shift は同じ実二単体の第零面。
方針：元全二単体の面式と厳密比較の全後合成式を使用。
規約：辺の類へ弱めない。使われ方：指定 connecting 境界。 -/
lemma dgIdentityHomGluingShiftedConnectingTriangle_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ (TS).diagram = curry (βs).homotopy.h := by
  exact (TS).face_zero.trans
    (congrArg curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_homotopyMap (β) (S)).symm)

/-- 概要：元長辺の逆 shift は同じ実二単体の第一面。
方針：元全二単体の面式と厳密比較の全後合成式を使用。
規約：辺の類へ弱めない。使われ方：指定元 connecting 長辺。 -/
lemma dgIdentityHomGluingShiftedConnectingTriangle_face_one :
    stdSimplex.δ (1 : Fin 3) ≫ (TS).diagram = curry (δs).homotopy.h := by
  exact (TS).face_one.trans
    (congrArg curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_homotopyMap (δ) (S)).symm)

/-- 概要：元前辺の逆 shift は同じ実二単体の第二面。
方針：元全二単体の面式と厳密比較の全後合成式を使用。
規約：辺の類へ弱めない。使われ方：元入力比較の指定境界。 -/
lemma dgIdentityHomGluingShiftedConnectingTriangle_face_two :
    stdSimplex.δ (2 : Fin 3) ≫ (TS).diagram = curry (αs).homotopy.h := by
  exact (TS).face_two.trans
    (congrArg curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_homotopyMap (α) (S)).symm)
end SerrePositivity.KST.SConstruction

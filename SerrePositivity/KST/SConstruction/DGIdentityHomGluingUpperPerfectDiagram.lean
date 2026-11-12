module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingUpperPerfectVertices

/-!
概要：元実逆回転の上二単体全体を元実 Perf nerve 内に保持する。
方針：元三頂点の証拠と D 正本の全図式持ち上げを使う。
規約：元全二単体と元三円柱を包含後に厳密回収する。
使われ方：元指定上二単体の第二段実評価と固定 ν 接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded InfinityCategories SSet
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


local notation "κ" => dgIdentityHomGluingStrictConeInputInvComparison R C F G a h
local notation "κs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (κ) (S)


local notation "GY" => G.comp (J)
local notation "FY" => F.comp (J)
local notation "AS" => DGFunctor.comp (A) (S)
local notation "BS" => DGFunctor.comp (B) (S)
local notation "FSS" => DGFunctor.comp (FS) (S)
local notation "γs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (κs) (δs)
local notation "RS" => dgModuleNaturalConeFunctor R C (BS) (FSS) (γs)
local notation "NS" => dgModuleNaturalInverseRotationSource R C (FY) (GY) (η)
local notation "q" => dgModuleNaturalConePrecomposition R C (BS) (AS) (FSS) (κs) (δs)
local notation "σ" => dgModuleNaturalInverseRotation R C (FY) (GY) (η)
local notation "ι" => dgModuleNaturalConeInr R C (BS) (FSS) (γs)
local notation "ιn" => dgModuleNaturalConeInr R C (AS) (FSS) (δs)
local notation "λ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ιn) (σ)

local notation "ρ" => dgIdentityHomGluingInverseRotationUpperRawComparison R C F G a h

local notation "T" => dgIdentityHomGluingInverseRotationUpperRawTriangle R C F G a h

/-- 概要：元上二単体の全頂点は同じ実 Perf 内にある。
方針：元三頂点の証拠を元二単体の両側面で回収する。
規約：元全二単体を保持。使われ方：元実図式の全像制限。 -/
lemma dgIdentityHomGluingInverseRotationUpper_perfect_vertices :
    ∀ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P ⊗ (Δ[2] : SSet.{max (u + 1) v})) _⦋0⦌,
      modulePerfectProjectiveOver R C Set.univ (((uncurry (T).diagram).app _ z).obj 0) := by
  apply perfectFunctorCompositionTriangle_vertices R C (T)
  · intro x
    exact dgIdentityHomGluingInverseRotationUpperFirst_perfect R C F (x.obj 0)
  · intro x
    exact dgIdentityHomGluingInverseRotationUpperMiddle_perfect R C F G a h (x.obj 0)
  · intro x
    exact dgIdentityHomGluingInverseRotationUpperLast_perfect R C G (x.obj 0)

/-- 概要：元上二単体全体の同じ実 Perf 内での図式。
方針：元全頂点の証拠により同じ全図式を充満部分圏へ制限する。
規約：別の二単体を選択しない。使われ方：第二段実評価の元上面。 -/
def dgIdentityHomGluingInverseRotationUpperPerfectDiagram :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P ⊗ (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift R (RightModule R C) (modulePerfectProjectiveOver R C Set.univ)
    (uncurry (T).diagram) (dgIdentityHomGluingInverseRotationUpper_perfect_vertices R C F G a h)

/-- 概要：元 Perf 上二単体は包含後に元全二単体を厳密回収する。
方針：D 正本の全包含回収を使う。
規約：元三円柱も全図式の制限として保持。使われ方：元指定上面の全比較。 -/
lemma dgIdentityHomGluingInverseRotationUpperPerfectDiagram_inclusion :
    dgIdentityHomGluingInverseRotationUpperPerfectDiagram R C F G a h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R C Set.univ) = uncurry (T).diagram :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp R (RightModule R C) (modulePerfectProjectiveOver R C Set.univ)
    (uncurry (T).diagram) (dgIdentityHomGluingInverseRotationUpper_perfect_vertices R C F G a h)
end SerrePositivity.KST.SConstruction

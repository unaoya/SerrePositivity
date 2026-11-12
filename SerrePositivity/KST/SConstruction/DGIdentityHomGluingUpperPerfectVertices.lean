module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperNative
public import SerrePositivity.KST.SConstruction.DGPerfectTriangleLift
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations

/-!
概要：元実逆回転の上二単体の三頂点が同じ実 Perf 内にあることを確認する。
方針：元代表・元実 perfect cone と既存の shift・cone 閉性を使用する。
規約：元加群・指定逆・負符号を持つ三辺を変更しない。
使われ方：元上二単体全体の Perf 内への持ち上げ。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories SSet
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

/-- 概要：元上二単体の第一頂点は元代表の二重 shift として実 perfect。
方針：元代表の射影性と perfect 性に既存 shift 閉性を二回適用する。
規約：元実対象を保持。使われ方：元上二単体の第一頂点持ち上げ。 -/
lemma dgIdentityHomGluingInverseRotationUpperFirst_perfect (x : P) :
    modulePerfectProjectiveOver R C Set.univ ((FSS).obj x) := by
  exact modulePerfectProjectiveOver_shift R C
    (modulePerfectProjectiveOver_shift R C
      ⟨representable_homotopicallyProjective R C (F.obj x),
        modulePerfectOver_representable R C (F.obj x) (Set.mem_univ _)⟩ 1) (-1)

/-- 概要：元上二単体の第二頂点は元実 cone の shift と第一頂点の実 cone。
方針：元 gluing cone に保持された perfect 証拠と既存の有限操作を使う。
規約：元比較の cone を置換しない。使われ方：元上二単体の第二頂点持ち上げ。 -/
lemma dgIdentityHomGluingInverseRotationUpperMiddle_perfect (x : P) :
    modulePerfectProjectiveOver R C Set.univ ((RS).obj x) := by
  have hb : modulePerfectProjectiveOver R C Set.univ ((B).obj x) :=
    (((dgIdentityHomGluingFunctor R C F G a h).comp
      (dgHomGluingConeFunctor R C C C (DGFunctor.id C) (DGFunctor.id C))).obj x).property
  exact modulePerfectProjectiveOver_cone R C
    (modulePerfectProjectiveOver_shift R C hb (-1))
    (dgIdentityHomGluingInverseRotationUpperFirst_perfect R C F x)
    (dgModuleNaturalConeArrow R C (BS) (FSS) (γs) x)

/-- 概要：元上二単体の終頂点は元代表そのものとして実 perfect。
方針：元代表の射影性と perfect 性を使う。
規約：元実対象を保持。使われ方：元上二単体の終頂点持ち上げ。 -/
lemma dgIdentityHomGluingInverseRotationUpperLast_perfect (x : P) :
    modulePerfectProjectiveOver R C Set.univ ((GY).obj x) :=
  ⟨representable_homotopicallyProjective R C (G.obj x),
    modulePerfectOver_representable R C (G.obj x) (Set.mem_univ _)⟩
end SerrePositivity.KST.SConstruction

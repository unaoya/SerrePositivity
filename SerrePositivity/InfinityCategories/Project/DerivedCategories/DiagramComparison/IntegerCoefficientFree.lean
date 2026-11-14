module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCoefficientComplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：任意の宇宙の整数自由化を係数移送した全関手と、元の A 自由化を比較する。
方針：指定生成元による随伴と係数拡大随伴を合成し、単位を保つ自然同型を取る。
規約：同型は全写像に自然で、生成元評価の単位を保持する。
使われ方：HA 1.2.4、G10 の整数 EZ 模型と A 線形化した積重みの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 指定整数生成元による実 Hom 同値。 -/
def integerLinearizationHomEquiv (X : Type u) (M : ModuleCat.{u} ℤ) :
    (integerLinearization.obj X ⟶ M) ≃ (X ⟶ (forget (ModuleCat.{u} ℤ)).obj M) where
  toFun f := ↾fun x => f (integerGenerator x)
  invFun f := integerLinearizationDesc f
  left_inv f := integerLinearization_hom_ext (by intro x; simp)
  right_inv f := by ext x; simp

/-- 任意の宇宙の指定整数自由化と忘却の随伴。 -/
def integerLinearizationAdjunction :
    integerLinearization.{u} ⊣ forget (ModuleCat.{u} ℤ) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := integerLinearizationHomEquiv
    homEquiv_naturality_left_symm := by
      intro X Y M f g
      apply integerLinearization_hom_ext
      intro x
      simp [integerLinearizationHomEquiv] }

/-- 同宇宙の整数係数環を経由した自由化も、元の A 忘却の左随伴。 -/
def integerCoefficientFreeAdjunction {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) :
    integerLinearization ⋙ simplicialRingIntegerModuleEquivalence.functor ⋙
      ModuleCat.extendScalars φ ⊣ forget (ModuleCat A) :=
  integerLinearizationAdjunction.comp
    (simplicialRingIntegerModuleEquivalence.toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj φ))

/-- 指定生成元の随伴で正規化した、係数移送と自由化の全自然同型。 -/
def integerCoefficientFreeIso {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) :
    integerLinearization ⋙ simplicialRingIntegerModuleEquivalence.functor ⋙
      ModuleCat.extendScalars φ ≅ ModuleCat.free A :=
  (integerCoefficientFreeAdjunction φ).leftAdjointUniq (ModuleCat.adj A)

/-- 比較同型は指定された自由化の単位を保つ。 -/
theorem integerCoefficientFreeIso_unit {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (X : Type u) :
    (integerCoefficientFreeAdjunction φ).unit.app X ≫
        (forget (ModuleCat A)).map ((integerCoefficientFreeIso φ).hom.app X) =
      (ModuleCat.adj A).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- 指定単位の生成元の像は、元の A 自由加群の標準生成元。 -/
theorem integerCoefficientFreeIso_generator {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (X : Type u) (x : X) :
    ((integerCoefficientFreeIso φ).hom.app X)
      ((integerCoefficientFreeAdjunction φ).unit.app X x) = ModuleCat.freeMk x := by
  exact congrArg (fun f : X ⟶ (forget (ModuleCat A)).obj ((ModuleCat.free A).obj X) => f x)
    (integerCoefficientFreeIso_unit φ X)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace

/-!
概要：積上の族と内部 Hom の族を指数則で相互に移し、元の制限と後合成を保つ。
方針：全パラメータの指数則と相対持ち上げを、元の図式の全境界へ移す。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限比較辺の局所性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の積図式の族を、第一因子上の関手の族へ curry する。 -/
def tensorFamilyCurry {A K T E : SSet.{u}} (H : (A ⊗ K) ⊗ T ⟶ E) :
    K ⊗ T ⟶ (ihom A).obj E := curry ((α_ A K T).inv ≫ H)

/-- 第一因子上の関手の族を、元の積図式の族へ展開する。 -/
def tensorFamilyUncurry {A K T E : SSet.{u}} (h : K ⊗ T ⟶ (ihom A).obj E) :
    (A ⊗ K) ⊗ T ⟶ E := (α_ A K T).hom ≫ uncurry h

/-- 積の族を展開して curry すると元の同じ族を回収する。 -/
lemma tensorFamilyCurry_uncurry {A K T E : SSet.{u}} (h : K ⊗ T ⟶ (ihom A).obj E) :
    tensorFamilyCurry (tensorFamilyUncurry h) = h := by
  simp only [tensorFamilyCurry, tensorFamilyUncurry, Iso.inv_hom_id_assoc, curry_uncurry]

/-- 積の族を curry して展開すると元の同じ図式を回収する。 -/
lemma tensorFamilyUncurry_curry {A K T E : SSet.{u}} (H : (A ⊗ K) ⊗ T ⟶ E) :
    tensorFamilyUncurry (tensorFamilyCurry H) = H := by
  simp only [tensorFamilyCurry, tensorFamilyUncurry, uncurry_curry, Iso.hom_inv_id_assoc]

/-- 積の族の curry は元の図式を一意に定める。 -/
lemma tensorFamilyCurry_injective {A K T E : SSet.{u}} :
    Function.Injective (tensorFamilyCurry (A := A) (K := K) (T := T) (E := E)) := by
  intro f g h
  simpa only [tensorFamilyUncurry_curry] using congrArg tensorFamilyUncurry h

/-- 積の族の curry は標的の射による後合成と可換。 -/
lemma tensorFamilyCurry_post {A K T E B : SSet.{u}} (H : (A ⊗ K) ⊗ T ⟶ E) (p : E ⟶ B) :
    tensorFamilyCurry (H ≫ p) = tensorFamilyCurry H ≫ (ihom A).map p := by
  apply uncurry_injective
  rw [tensorFamilyCurry, uncurry_curry, uncurry_natural_right,
    tensorFamilyCurry, uncurry_curry, Category.assoc]

/-- 積の族の curry は第一因子の元の制限と可換。 -/
lemma tensorFamilyCurry_source {A D K T E : SSet.{u}} (i : D ⟶ A)
    (H : (A ⊗ K) ⊗ T ⟶ E) :
    tensorFamilyCurry (((i ▷ K) ▷ T) ≫ H) =
      tensorFamilyCurry H ≫ (pre i).app E := by
  apply uncurry_injective
  rw [tensorFamilyCurry, uncurry_curry, uncurry_pre_app, tensorFamilyCurry, uncurry_curry]
  rfl

/-- 積の族の curry はパラメータの元の制限と可換。 -/
lemma tensorFamilyCurry_parameter {A K T S E : SSet.{u}} (j : S ⟶ T)
    (H : (A ⊗ K) ⊗ T ⟶ E) :
    tensorFamilyCurry (((A ⊗ K) ◁ j) ≫ H) = (K ◁ j) ≫ tensorFamilyCurry H := by
  apply uncurry_injective
  rw [tensorFamilyCurry, uncurry_curry, uncurry_natural_left, tensorFamilyCurry, uncurry_curry]
  rfl

/-- 固定した底の積図式は、同じ底の関手の定値パラメータ族へ移る。 -/
lemma tensorFamilyCurry_constant {A K T B : SSet.{u}} (g : A ⊗ K ⟶ B) :
    tensorFamilyCurry (fst (A ⊗ K) T ≫ g) = fst K T ≫ curry g := by
  apply uncurry_injective
  rw [tensorFamilyCurry, uncurry_curry, uncurry_natural_left, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

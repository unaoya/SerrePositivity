module
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHom

/-!
概要：自然性条件つきの Hom 射の族を、図式 Hom 複体への射にまとめる。
方針：各次数で cochain を組み立て、評価と微分の可換性で鎖写像条件を確認する。
規約：点ごとの元の射を保持し、添字方向の条件を省略しない。
使われ方：HA 1.2.4、G10 の全単体テンソル Hom と図式 Hom の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
variable (P Q : J ⥤ Complex A) (T : Complex A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 自然性条件つき Hom 射の族の各元を、図式 cochain に組み立てる。 -/
def diagramHomFamilyCochain (g : DiagramHomFamily P Q T) (n : ℤ) (x : T.X n) :
    Cochain ((E).obj P) ((E).obj Q) n :=
  diagramCochainAssemble P Q (fun j => (g.val j).f n x) (by
    intro i j t p q hpq
    have h := congrArg (fun k => (k.f n x).v p q hpq) (g.property t)
    simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      homPrecompose_apply, homPostcompose_apply, Cochain.zero_cochain_comp_v,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h)

/-- 組み立てた cochain の評価は元の成分。 -/
theorem diagramHomFamilyCochain_at (g : DiagramHomFamily P Q T) (n : ℤ) (x : T.X n) (j : J) :
    diagramCochainAt P Q (diagramHomFamilyCochain P Q T g n x) j = (g.val j).f n x := rfl

/-- 自然性を持つ族から、元の図式 Hom 複体への鎖写像。 -/
def diagramHomFamilyLift (g : DiagramHomFamily P Q T) :
    T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q) where
  f n := ModuleCat.ofHom
    { toFun := diagramHomFamilyCochain P Q T g n
      map_add' := by
        intro x y
        apply diagramCochain_ext P Q
        intro j
        exact (g.val j).f n |>.hom.map_add x y
      map_smul' := by
        intro a x
        apply diagramCochain_ext P Q
        intro j
        exact (g.val j).f n |>.hom.map_smul a x }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply diagramCochain_ext P Q
    intro j
    change diagramCochainAt P Q (δ n m (diagramHomFamilyCochain P Q T g n x)) j = _
    rw [diagramCochainAt_delta, diagramHomFamilyCochain_at]
    exact ConcreteCategory.congr_hom ((g.val j).comm n m) x

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

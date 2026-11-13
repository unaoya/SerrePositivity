module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Products.DependentProductHomotopy
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：点つき単体集合の任意の小積の具体的な対象、射影、普遍性。
方針：次数ごとの依存関数に基点の族を与え、全ての式を評価で検査する。
規約：空積も含む。各段の Kan 性と全基点 π 同型の積の保存も公開する。
使われ方：BF 1978 §2、HA §1.4.2。Sp の任意の小積。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
namespace SerrePositivity.KST.Spectra.PointedSmallProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u}

/-- 基点を各座標の基点の族とする具体的な小積。 -/
def obj (X : S → PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (X s).hom))

/-- 指定した座標への点つき射影。 -/
def projection (X : S → PointedSimplicialSet.{u}) (s : S) : obj X ⟶ X s :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.eval S (fun s ↦ (X s).right) s)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval _ s)

/-- 点つき射の族を積へ束ねる。 -/
def lift {X : S → PointedSimplicialSet.{u}} {A : PointedSimplicialSet.{u}}
    (f : ∀ s, A ⟶ X s) : A ⟶ obj X :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (f s).right)) (by
    change A.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (f s).right) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift (fun s ↦ (X s).hom)
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
    intro s
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.lift_eval]
    exact Under.w (f s))

@[reassoc (attr := simp)]
lemma lift_projection {X : S → PointedSimplicialSet.{u}} {A : PointedSimplicialSet.{u}}
    (f : ∀ s, A ⟶ X s) (s : S) : lift f ≫ projection X s = f s := by
  apply Under.UnderMorphism.ext
  rfl

lemma hom_ext {X : S → PointedSimplicialSet.{u}} {A : PointedSimplicialSet.{u}}
    {f g : A ⟶ obj X} (h : ∀ s, f ≫ projection X s = g ≫ projection X s) : f = g := by
  apply Under.UnderMorphism.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.hom_ext
  intro s
  exact congrArg Under.Hom.right (h s)

/-- 具体的な積の射影からなる fan。 -/
def fan (X : S → PointedSimplicialSet.{u}) : Fan X := Fan.mk (obj X) (projection X)

/-- 具体的な小積の点つき普遍性。 -/
def isLimit (X : S → PointedSimplicialSet.{u}) : IsLimit (fan X) :=
  Fan.IsLimit.mk _ (fun s ↦ lift (fun j ↦ s.proj j)) (fun _ _ ↦ lift_projection _ _)
    (fun _ _ hm ↦ hom_ext (fun j ↦ (hm j).trans (lift_projection _ j).symm))

/-- 小積の各値の Kan 性は座標ごとの充填から得られる。 -/
instance kanComplex (X : S → PointedSimplicialSet.{u}) [∀ s, KanComplex (X s).right] :
    KanComplex (obj X).right :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialDependentProduct.kanComplex S (fun s ↦ (X s).right)

/-- 族の点つき射の積。 -/
def map {X Y : S → PointedSimplicialSet.{u}} (f : ∀ s, X s ⟶ Y s) : obj X ⟶ obj Y :=
  lift (fun s ↦ projection X s ≫ f s)

@[reassoc (attr := simp)]
lemma map_projection {X Y : S → PointedSimplicialSet.{u}} (f : ∀ s, X s ⟶ Y s) (s : S) :
    map f ≫ projection Y s = projection X s ≫ f s := lift_projection _ _

/-- 全基点 π 同型は任意の点つき小積で保存される。 -/
lemma map_piIsomorphism {X Y : S → PointedSimplicialSet.{u}}
    [∀ s, KanComplex (X s).right] [∀ s, KanComplex (Y s).right]
    (f : ∀ s, X s ⟶ Y s) (hf : ∀ s, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f s).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (map f).right :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DependentProductHomotopy.map_piIsomorphism (fun s ↦ (X s).right)
    (fun s ↦ (f s).right) hf

end
end SerrePositivity.KST.Spectra.PointedSmallProduct

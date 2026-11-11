module
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso
public import Mathlib.CategoryTheory.EqToHom

/-! # 対象等号の移送である実際の射
概要：対象等号から得る射の合成・関手像・具体的 cube tensor を照合する。
方針：実際の射が eqToHom である等号の証人を保持し、元の両端で比較する。
規約：任意の可逆射が対象等号とは仮定しない。使われ方：元の tensor 比較の coherence。
-/
@[expose] public section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の射そのものが、対象等号による移送であること。 -/
def IsObjectEqualityMap {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ h : X = Y, f = eqToHom h

/-- 元の恒等射は対象等号の移送。 -/
lemma objectEqualityMap_id {C : Type u} [Category.{v} C] (X : C) :
    IsObjectEqualityMap (𝟙 X) := ⟨rfl, rfl⟩

/-- 元の対象等号の射には同じ等号の証人がある。 -/
lemma objectEqualityMap_eqToHom {C : Type u} [Category.{v} C] {X Y : C} (h : X = Y) :
    IsObjectEqualityMap (eqToHom h) := ⟨h, rfl⟩

/-- 元の移送射の合成も、同じ元の両端の対象等号による移送。 -/
lemma objectEqualityMap_comp {C : Type u} [Category.{v} C] {X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsObjectEqualityMap f) (hg : IsObjectEqualityMap g) :
    IsObjectEqualityMap (f ≫ g) := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨k, rfl⟩ := hg
  exact ⟨h.trans k, eqToHom_trans h k⟩

/-- 元の関手は、対象等号による実際の移送射を保つ。 -/
lemma objectEqualityMap_map {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} (hf : IsObjectEqualityMap f) :
    IsObjectEqualityMap (F.map f) := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨congrArg F.obj h, eqToHom_map F h⟩

/-- 同じ両端の対象等号の移送射は、実際の射として等しい。 -/
lemma objectEqualityMap_eq {C : Type u} [Category.{v} C] {X Y : C} {f g : X ⟶ Y}
    (hf : IsObjectEqualityMap f) (hg : IsObjectEqualityMap g) : f = g := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨k, rfl⟩ := hg
  rfl

/-- 元の具体的 cube の次元同型は対象等号による移送。 -/
lemma concreteCubeDimensionIso_objectEqualityMap {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (h : X.dimension = Y.dimension) : IsObjectEqualityMap (concreteCubeDimensionIso h).hom := by
  cases X
  cases Y
  cases h
  exact objectEqualityMap_id _

/-- 元の具体的 cube tensor は両側の実際の移送射を保つ。 -/
lemma concreteCubeTensor_objectEqualityMap {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    {f : X ⟶ X'} {g : Y ⟶ Y'} (hf : IsObjectEqualityMap f) (hg : IsObjectEqualityMap g) :
    IsObjectEqualityMap (concreteCubeTensorMap f g) := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨k, rfl⟩ := hg
  exact ⟨congrArg₂ concreteCubeTensorObj h k, concreteCubeTensorMap_eqToHom h k⟩

end SerrePositivity.KST.SConstruction

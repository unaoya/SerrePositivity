module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldInverseFamily
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramScaffoldIdentities

/-!
概要：水平辺を保つ scaffold Hom から strict transport 間の変換空間への逆射を構成する。
方針：under 評価から得た cocartesian section の族を curry し、元の逆射の自然性を使う。
規約：全対象・全次数で一つの単体集合の射とし、元の相対 Hom の逆射と包含後に照合する。
使われ方：cocartesian scaffold の写像空間比較の厳密な同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 逆比較の各成分を全 section 空間へ含めると、元の scaffold の逆比較と一致する。 -/
lemma cocartesianScaffoldInverseComponent_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C) :
    cocartesianScaffoldInverseComponent F q c ≫
      (ihom (F.obj c)).map (SerrePositivity.InfinityCategories.cocartesianSectionsι q (nerveMap (Under.forget c))) =
      cocartesianScaffoldFunctorInclusion F q ≫ strictDiagramScaffoldInverseComponent F q c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro l β
  apply ConcreteCategory.hom_ext
  intro τ
  rfl

/-- 逆比較の成分を任意の二つのパラメーターで評価し、包含後に元の逆比較と照合する。 -/
lemma cocartesianScaffoldInverseComponent_app_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) (c : C)
    (n k : SimplexCategoryᵒᵖ) (v : (CocartesianScaffoldFunctorSpace F q).obj n)
    (α : n ⟶ k) (x : (F.obj c).obj k) :
    (((cocartesianScaffoldInverseComponent F q c).app n v).app k α x).val =
      (((strictDiagramScaffoldInverseComponent F q c).app n v.val).app k α x) := by
  exact congrArg (fun H : CocartesianScaffoldFunctorSpace F q ⟶
      (ihom (F.obj c)).obj (leftStrictTransport q c) => (H.app n v).app k α x)
    (cocartesianScaffoldInverseComponent_ι F q c)

/-- 水平辺を保つ相対関手の単体から、同じ次数の cocartesian section の変換を得る。 -/
def cocartesianDiagramScaffoldInverseSimplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C)
    {n : SimplexCategoryᵒᵖ} (v : (CocartesianScaffoldFunctorSpace F q).obj n) :
    strictDiagramMappingSimplex F (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram q) n :=
   ⟨fun c ↦ (cocartesianScaffoldInverseComponent F q c).app n v, by
    intro c d f k α x
    apply Subtype.ext
    change ((leftStrictTransportDiagram q).map f).app k
        (((cocartesianScaffoldInverseComponent F q c).app n v).app k α x).val =
      (((cocartesianScaffoldInverseComponent F q d).app n v).app k α ((F.map f).app k x)).val
    rw [cocartesianScaffoldInverseComponent_app_ι, cocartesianScaffoldInverseComponent_app_ι]
    exact ((strictDiagramMappingScaffoldInverse F q).app n v.val).property f k α x⟩

/-- 水平辺を保つ相対関手の全空間から、同じ cocartesian strict transport への全変換を回収する。 -/
def cocartesianDiagramScaffoldMappingSpaceInverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {D : SSet.{u}} (q : D ⟶ nerve C) :
    CocartesianScaffoldFunctorSpace F q ⟶
      strictDiagramMappingSpace F (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram q) where
  app _ := ↾cocartesianDiagramScaffoldInverseSimplex F q
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro k β
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change (((cocartesianScaffoldInverseComponent F q c).app m
        ((CocartesianScaffoldFunctorSpace F q).map α v)).app k β x).val =
      (((cocartesianScaffoldInverseComponent F q c).app n v).app k (α ≫ β) x).val
    rw [cocartesianScaffoldInverseComponent_app_ι, cocartesianScaffoldInverseComponent_app_ι]
    exact congrArg (fun z => z.app k β x)
      (ConcreteCategory.congr_hom
        ((strictDiagramScaffoldInverseComponent F q c).naturality α) v.val)

end SerrePositivity.InfinityCategories

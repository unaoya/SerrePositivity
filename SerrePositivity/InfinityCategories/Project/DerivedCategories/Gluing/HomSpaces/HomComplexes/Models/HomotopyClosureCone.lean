module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ConeHomotopyRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.YonedaHomotopyFull

/-! 標準 Yoneda 円錐の表現可能性を、K(Gluing) の同型閉包の円錐閉性へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "H" => ModuleHomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => moduleToHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
variable (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD

/-- 任意の distinguished 三角形で、最初の二対象の表現可能性は第三へ移る。 -/
lemma dgGluingRepresentableProperty_cone (T : Triangle H) (hT : T ∈ distTriang H)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) : P T.obj₃ := by
  obtain ⟨X, ⟨eX⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R G _).1 h₁
  obtain ⟨Y, ⟨eY⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R G _).1 h₂
  let fk := eX.inv ≫ T.mor₁ ≫ eY.hom
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaHomotopy_map_surjective R G X Y fk
  let S := moduleHomotopyConeTriangle R G ((dgYoneda R G).onClosed.map f)
  have hS : S ∈ distTriang H :=
    moduleHomotopyConeTriangle_distinguished R G ((dgYoneda R G).onClosed.map f)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChosenConeHomotopyRepresentable R C D M X Y f hC hD
  change P S.obj₃ at hc
  have hcomm : T.mor₁ ≫ eY.hom = eX.hom ≫ S.mor₁ := by
    change T.mor₁ ≫ eY.hom = eX.hom ≫ (K).map ((dgYoneda R G).onClosed.map f)
    rw [hf]
    simp only [fk, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let e := isoTriangleOfIso₁₂ T S hT hS eX eY hcomm
  exact (P).prop_of_iso ((Triangle.π₃).mapIso e).symm hc

/-- 同型閉包の全円錐閉性を、三角的対象条件の型で供給。 -/
lemma dgGluingRepresentable_isTriangulatedClosed₃ : (P).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ :=
    ⟨T.obj₃, dgGluingRepresentableProperty_cone R C D M hC hD T hT h₁ h₂, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

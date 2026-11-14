module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFamilyYonedaNaturality
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
/-!
概要：ラベルの実評価での cone のホモトピー代表を、ラベル圏の Yoneda cone へ戻す。
方針：同じ Yoneda 自然比較と標準 distinguished triangle の二頂点比較を使う。
規約：実加群の厳密同型による cone 閉性を仮定せず、ホモトピー代表を保持する。
使われ方：c′ の演算精密化を D-8 b の cone 判定へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (I : Type w) [Small.{u} I] (value : I → RightModule R D)

lemma dgModuleFamilyYonedaCone_homotopyRepresentable :
    letI := inducedDGCategory R value
    ∀ {X Y : ClosedCategory R I} (f : X ⟶ Y) (k : I),
      Nonempty ((moduleToHomotopy R D).obj
        (moduleCone R D ((inducedDGEvaluation R value).onClosed.map f)) ≅
          (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R) (value k))) →
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R I (ForgetEnrichment.to (Complex R)
        (moduleCone R I ((dgYoneda R I).onClosed.map f))) := by
  letI := inducedDGCategory R value
  intro X Y f k h
  obtain ⟨h⟩ := h
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFamilyYoneda R D I value
  let E := inducedDGEvaluation R value
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFamilyYonedaClosedIso R D I value
  let K := moduleToHomotopy R I
  let g := F.onClosed.map (E.onClosed.map f)
  let T := moduleHomotopyConeTriangle R I g
  let U := moduleHomotopyConeTriangle R I ((dgYoneda R I).onClosed.map f)
  have hcomm : T.mor₁ ≫ (K.mapIso (e.app Y)).hom =
      (K.mapIso (e.app X)).hom ≫ U.mor₁ := by
    change K.map g ≫ K.map (e.app Y).hom =
      K.map (e.app X).hom ≫ K.map ((dgYoneda R I).onClosed.map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg K.map (e.hom.naturality f)
  let ec := (Triangle.π₃).mapIso (isoTriangleOfIso₁₂ T U
    (moduleHomotopyConeTriangle_distinguished R I g)
    (moduleHomotopyConeTriangle_distinguished R I ((dgYoneda R I).onClosed.map f))
    (K.mapIso (e.app X)) (K.mapIso (e.app Y)) hcomm)
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R I _).mpr
  exact ⟨k, ⟨ec.symm ≪≫ K.mapIso
    (DGFunctor.moduleValuedConeIso R D I F (E.onClosed.map f)) ≪≫
    F.onHomotopy.mapIso h ≪≫ K.mapIso (eqToIso (congrArg
      (ForgetEnrichment.of (Complex R)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFamilyYoneda_obj R D I value k)))⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories

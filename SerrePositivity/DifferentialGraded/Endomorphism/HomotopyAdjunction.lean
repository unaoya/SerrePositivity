module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleAdjunction

/-! # 指定対象による再構成随伴の主ホモトピー圏への降下

dg関手が境界を保つことを使い、単位・余単位と三角恒等式を商へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成単位を主K(End(E))へ送る。 -/
def endomorphismHomotopyUnit :
    𝟭 (ModuleHomotopyCategory A (EndomorphismObject E)) ⟶
      (endomorphismModuleTensor A D E).onHomotopy ⋙
        (endomorphismModuleHom A D E).onHomotopy where
  app X := (moduleToHomotopy A (EndomorphismObject E)).map
    ((endomorphismModuleUnit A D E).app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (moduleToHomotopy A (EndomorphismObject E)).map_surjective f
    change (moduleToHomotopy A (EndomorphismObject E)).map f ≫
        (moduleToHomotopy A (EndomorphismObject E)).map ((endomorphismModuleUnit A D E).app Y) =
      (moduleToHomotopy A (EndomorphismObject E)).map ((endomorphismModuleUnit A D E).app X) ≫
        (moduleToHomotopy A (EndomorphismObject E)).map
          ((endomorphismModuleHom A D E).onClosed.map
            ((endomorphismModuleTensor A D E).onClosed.map f))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).naturality f)

/-- 再構成余単位を主K(D)へ送る。 -/
def endomorphismHomotopyCounit :
    (endomorphismModuleHom A D E).onHomotopy ⋙
      (endomorphismModuleTensor A D E).onHomotopy ⟶ 𝟭 (ModuleHomotopyCategory A D) where
  app X := (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app X.as)
  naturality {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
    change (moduleToHomotopy A D).map
        ((endomorphismModuleTensor A D E).onClosed.map
          ((endomorphismModuleHom A D E).onClosed.map f)) ≫
        (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app Y) =
      (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app X) ≫
        (moduleToHomotopy A D).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).naturality f)

lemma endomorphismHomotopy_left_triangle (X : ModuleHomotopyCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onHomotopy.map ((endomorphismHomotopyUnit A D E).app X) ≫
      (endomorphismHomotopyCounit A D E).app
        ((endomorphismModuleTensor A D E).onHomotopy.obj X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (moduleToHomotopy A D).map
      ((endomorphismModuleTensor A D E).onClosed.map ((endomorphismModuleUnit A D E).app X)) ≫
    (moduleToHomotopy A D).map ((endomorphismModuleCounit A D E).app
      ((endomorphismModuleTensor A D E).onClosed.obj X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, endomorphismModule_left_triangle,
    CategoryTheory.Functor.map_id]

lemma endomorphismHomotopy_right_triangle (X : ModuleHomotopyCategory A D) :
    (endomorphismHomotopyUnit A D E).app ((endomorphismModuleHom A D E).onHomotopy.obj X) ≫
      (endomorphismModuleHom A D E).onHomotopy.map
        ((endomorphismHomotopyCounit A D E).app X) = 𝟙 _ := by
  obtain ⟨X⟩ := X
  change (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).app ((endomorphismModuleHom A D E).onClosed.obj X)) ≫
    (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map ((endomorphismModuleCounit A D E).app X)) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, endomorphismModule_right_triangle,
    CategoryTheory.Functor.map_id]

/-- 主ホモトピー圏間の再構成tensor–Hom随伴。 -/
def endomorphismHomotopyAdjunction :
    (endomorphismModuleTensor A D E).onHomotopy ⊣ (endomorphismModuleHom A D E).onHomotopy :=
  Adjunction.mkOfUnitCounit
    { unit := endomorphismHomotopyUnit A D E
      counit := endomorphismHomotopyCounit A D E
      left_triangle := by
        apply NatTrans.ext
        funext X
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismHomotopy_left_triangle A D E X
      right_triangle := by
        apply NatTrans.ext
        funext X
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismHomotopy_right_triangle A D E X }

end SerrePositivity.DifferentialGraded

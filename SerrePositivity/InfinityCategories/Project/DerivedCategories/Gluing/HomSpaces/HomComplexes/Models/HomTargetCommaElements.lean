module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCommaComponents
/-!
概要：元終域への comma Hom 比較の三成分を全次数の元で評価する。
方針：鎖写像・cochain の厳密な成分等式を同じ次数で評価する。
規約：元の左右関手の Hom 作用と第三成分を保持する。
使われ方：全次数合成の保存を元の二作用の式に帰着する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
variable (n : ℤ) (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X n)
lemma dgGluingHomTargetCommaHomMap_source_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D E q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f n a) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y).f n a := by
  have h := congrArg (fun f => f.f n a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_source R C D E p q X Y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact h
lemma dgGluingHomTargetCommaHomMap_replacement_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D E q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f n a) =
    (p.map X.left Y.left).f n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y).f
        n a) := by
  have h := congrArg (fun f => f.f n a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_replacement R C D E p q X Y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact h
lemma dgGluingHomTargetCommaHomMap_image_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D E q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f n a) =
    (q.map X.right Y.right).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y).f n a) := by
  exact congrArg ((q.map X.right Y.right).f n)
    (dgGluingHomTargetCommaHomMap_source_element R C D E p q X Y n a)
lemma dgGluingHomTargetCommaHomMap_primitive_element :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D E q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaObject R C D E p q Y)).v n (n - 1) (by omega)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap R C D E p q X Y).f n a) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y).v n (n - 1) (by omega) a :=
        by
  have h := Cochain.congr_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCommaHomMap_comparison R C D E p q X Y)
    n (n - 1) (by omega)
  have he := congrArg (fun f => f a) h
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ModuleCat.comp_apply] at he
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

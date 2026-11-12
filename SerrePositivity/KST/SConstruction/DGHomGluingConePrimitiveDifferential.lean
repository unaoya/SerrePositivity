module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeComponents
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 元の第三成分の Yoneda 像の微分
概要：元の gluing の比較差を同じ実加群 Hom の合成として回収する。
方針：元の境界式を Yoneda で写し、全 Hom の合成保存を使う。
規約：元の閉比較射を保持。使われ方：実 cone Hom 鎖写像の微分照合。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 同じ第三 cochain の成分は、元の第三成分の Yoneda 像そのもの。 -/
lemma dgHomGluingConePrimitive_apply (i j : ℤ) (hij : i + (-1) = j)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X i) :
    (dgHomGluingConePrimitive R C D E p q X Y).v i j hij a =
      ((dgYoneda R E).map (p.obj X.left) (q.obj Y.right)).f j
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D _ X Y).v i j hij a) := by
  exact cochain_comp_ofHom_apply
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y)
    ((dgYoneda R E).map (p.obj X.left) (q.obj Y.right)) hij a

/-- 第三成分の捻れた微分は元の左右像と元の比較射の実加群 Hom 合成を回収する。 -/
lemma dgHomGluingConePrimitive_differential (n : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X n) :
    (dgHomGluingConePrimitive R C D E p q X Y).v (n + 1) n (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D _ X Y).d n (n + 1) a) =
      compose R (x := representable R (p.obj X.left))
        (y := representable R (p.obj Y.left)) (z := representable R (q.obj Y.right))
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
          (dgHomGluingTargetModuleMap R C D E p q Y))).val
        ((dgHomGluingConeLeftMap R C D E p q X Y).f n a) (add_zero n) -
      compose R (x := representable R (p.obj X.left))
        (y := representable R (q.obj X.right)) (z := representable R (q.obj Y.right))
        ((dgHomGluingConeRightMap R C D E p q X Y).f n a)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
          (dgHomGluingTargetModuleMap R C D E p q X))).val (zero_add n) -
      (moduleHom R E (representable R (p.obj X.left))
        (representable R (q.obj Y.right))).d (n - 1) n
          ((dgHomGluingConePrimitive R C D E p q X Y).v n (n - 1) (by omega) a) := by
  simp only [dgHomGluingConePrimitive_apply, dgHomGluingTargetModuleMap_cycle]
  rw [dgGluingPrimitive_differential]
  erw [map_sub, map_sub, dgHomGluingLeftAction_apply, dgHomGluingRightAction_apply]
  erw [DGFunctor.map_forward, DGFunctor.map_forward]
  have hd := ConcreteCategory.congr_hom
    (((dgYoneda R E).map (p.obj X.left) (q.obj Y.right)).comm (n - 1) n)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D (dgHomGluingBimodule R C D E p q) X Y).v
      n (n - 1) (by omega) a)
  erw [← hd]
  simp only [dgHomGluingConeLeftMap, dgHomGluingConeRightMap,
    HomologicalComplex.comp_f, ModuleCat.comp_apply, compose,
    mul_zero, zero_mul, Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.KST.SConstruction

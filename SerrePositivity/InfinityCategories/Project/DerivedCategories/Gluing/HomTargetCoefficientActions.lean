module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCoefficientPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedModelInverseNaturality
/-!
概要：元終域への係数 path の両端を、元二脚と元閉比較射の前後合成へ照合する。
方針：全 Hom 鎖写像の二作用式を実 Hom 模型同型の自然性へ渡す。
規約：対象や H⁰ の比較へ弱めず、左右の全次数入力を保つ。
使われ方：元終域の二つの合成三角形と mapping cocone path の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetLeftCoefficientInput :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (p.map X.left Y.left) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) (p.obj X.left) (p.obj Y.left)).inv

def dgGluingHomTargetRightCoefficientInput :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (q.map X.right Y.right) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) (q.obj X.right) (q.obj Y.right)).inv

/-- 左端は元 p の全 Hom 作用の後に元の標的 augmentation を合成する。 -/
lemma dgGluingHomTargetLeftCoefficientAction :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom =
    dgGluingHomTargetLeftCoefficientInput R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := E) (E := E)
        (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (p.obj X.left))
          (dgHomGluingTargetMap R C D E p q Y)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso, Iso.symm_hom,
    dgGluingHomTargetLeftCoefficientInput]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_leftAction R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality (C := E) (D := E)
      (x := p.obj X.left) (y := p.obj Y.left)
      (x' := p.obj X.left) (y' := q.obj Y.right)
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (p.obj X.left))
        (dgHomGluingTargetMap R C D E p q Y))]
  simp only [Category.assoc]

/-- 右端は元 q の全 Hom 作用の前に元の始域 augmentation を合成する。 -/
lemma dgGluingHomTargetRightCoefficientAction :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom =
    dgGluingHomTargetRightCoefficientInput R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := E) (E := E)
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgHomGluingTargetMap R C D E p q X)
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (q.obj Y.right))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso, Iso.symm_hom,
    dgGluingHomTargetRightCoefficientInput]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_rightAction R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality (C := E) (D := E)
      (x := q.obj X.right) (y := q.obj Y.right)
      (x' := p.obj X.left) (y' := q.obj Y.right)
      (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgHomGluingTargetMap R C D E p q X)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (q.obj Y.right)))]
  simp only [Category.assoc]

/-- 元終域の path の両端は、元二脚と元 augmentation の全作用の積。 -/
lemma dgGluingHomTargetCoefficientInputPair_actions :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPair R C D E p q X Y =
      (dgGluingHomTargetLeftCoefficientInput R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := E) (E := E)
          (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (p.obj X.left))
            (dgHomGluingTargetMap R C D E p q Y))) ⊗ₘ
      (dgGluingHomTargetRightCoefficientInput R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := E) (E := E)
          (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgHomGluingTargetMap R C D E p q X)
            (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (q.obj Y.right)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPair, tensorHom_comp_tensorHom,
    dgGluingHomTargetLeftCoefficientAction, dgGluingHomTargetRightCoefficientAction]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

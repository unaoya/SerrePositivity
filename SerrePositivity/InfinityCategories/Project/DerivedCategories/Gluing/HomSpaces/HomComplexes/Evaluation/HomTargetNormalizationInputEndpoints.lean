module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Evaluation.HomTargetInputTriangleEvaluations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Evaluation.HomTargetCollarTriangleEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetStandardCapTriangles
/-!
概要：元入力付き四補正道の元端と共通補正端を、実三角形全体で同定する。
方針：三角形評価と元鎖射影の二つの厳密等式を外延性へ渡す。
規約：指定矢印比較の元端を変えない。使われ方：相対二次元比較の三辺の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPreNormalizationInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowFirstInputLift R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCollarTriangle_one R C D E p q X Y).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowFirstInputLift_triangle R C D E p q X Y).symm)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath_over.{u, v} R C D E p q X Y, ← Category.assoc,
      ι₁_fst, Category.id_comp]
    exact (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm

lemma dgGluingHomTargetExitCollarInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowLastInputLift R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarTriangle_zero R C D E p q X Y).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowLastInputLift_triangle R C D E p q X Y).symm)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath_over.{u, v} R C D E p q X Y, ← Category.assoc,
      ι₀_fst, Category.id_comp]
    exact (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm

lemma dgGluingHomTargetPreCapInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y =
      ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · have hcap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y)
    have hbase := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y)
    exact hcap.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily_zero.{u, max (u + 1) v} R E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans hbase.symm)
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath_over,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath_over.{u, v} R C D E p q X Y]

lemma dgGluingHomTargetExitCapInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y =
      ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · have hcap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y)
    have hbase := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y)
    exact hcap.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily_one.{u, max (u + 1) v} R E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans hbase.symm)
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath_over,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath_over.{u, v} R C D E p q X Y]

lemma dgGluingHomTargetPreCapInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · have hcap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y)
    have hstandard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection_triangle R C D E p q X Y)
    exact hcap.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapTriangle_one_standard R C D E p q X Y).trans hstandard.symm)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath_over R C D E p q X Y,
      ← Category.assoc, ι₁_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputSection_input R C D E p q X Y, Category.comp_id]

lemma dgGluingHomTargetExitCapInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · have hcap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y)
    have hstandard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleEvaluation_precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection_triangle R C D E p q X Y)
    exact hcap.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapTriangle_zero_standard R C D E p q X Y).trans hstandard.symm)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath_over R C D E p q X Y,
      ← Category.assoc, ι₀_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputSection_input R C D E p q X Y, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

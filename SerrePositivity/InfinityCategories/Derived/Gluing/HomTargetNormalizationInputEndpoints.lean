module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputTriangleEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCollarTriangleEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetStandardCapTriangles
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPreNormalizationInputPath_one :
    ι₁ ≫ dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y =
      dgGluingHomTargetArrowFirstInputLift R C D E p q X Y := by
  apply dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · exact (dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y)).trans
        ((dgGluingHomTargetPreCollarTriangle_one R C D E p q X Y).trans
          (dgGluingHomTargetArrowFirstInputLift_triangle R C D E p q X Y).symm)
  · rw [Category.assoc, dgGluingHomTargetPreNormalizationInputPath_over.{u, v} R C D E p q X Y, ← Category.assoc,
      ι₁_fst, Category.id_comp]
    exact (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm

lemma dgGluingHomTargetExitCollarInputPath_zero :
    ι₀ ≫ dgGluingHomTargetExitCollarInputPath R C D E p q X Y =
      dgGluingHomTargetArrowLastInputLift R C D E p q X Y := by
  apply dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · exact (dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetExitCollarInputPath R C D E p q X Y)
      (dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y)).trans
        ((dgGluingHomTargetExitCollarTriangle_zero R C D E p q X Y).trans
          (dgGluingHomTargetArrowLastInputLift_triangle R C D E p q X Y).symm)
  · rw [Category.assoc, dgGluingHomTargetExitCollarInputPath_over.{u, v} R C D E p q X Y, ← Category.assoc,
      ι₀_fst, Category.id_comp]
    exact (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm

lemma dgGluingHomTargetPreCapInputPath_zero :
    ι₀ ≫ dgGluingHomTargetPreCapInputPath R C D E p q X Y =
      ι₀ ≫ dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y := by
  apply dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · have hcap := dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetPreCapInputPath R C D E p q X Y)
      (dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y)
    have hbase := dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y)
      (dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y)
    exact hcap.trans ((dgGluingPreUnitCapTriangleFamily_zero.{u, max (u + 1) v} R E
      (dgGluingHomTargetIdentityCommaObject R C D E p q X)
      (dgGluingHomTargetIdentityCommaObject R C D E p q Y)
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans hbase.symm)
  · simp only [Category.assoc, dgGluingHomTargetPreCapInputPath_over,
      dgGluingHomTargetPreNormalizationInputPath_over.{u, v} R C D E p q X Y]

lemma dgGluingHomTargetExitCapInputPath_one :
    ι₁ ≫ dgGluingHomTargetExitCapInputPath R C D E p q X Y =
      ι₁ ≫ dgGluingHomTargetExitCollarInputPath R C D E p q X Y := by
  apply dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · have hcap := dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetExitCapInputPath R C D E p q X Y)
      (dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y)
    have hbase := dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetExitCollarInputPath R C D E p q X Y)
      (dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y)
    exact hcap.trans ((dgGluingExitUnitCapTriangleFamily_one.{u, max (u + 1) v} R E
      (dgGluingHomTargetIdentityCommaObject R C D E p q X)
      (dgGluingHomTargetIdentityCommaObject R C D E p q Y)
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans hbase.symm)
  · simp only [Category.assoc, dgGluingHomTargetExitCapInputPath_over,
      dgGluingHomTargetExitCollarInputPath_over.{u, v} R C D E p q X Y]

lemma dgGluingHomTargetPreCapInputPath_one :
    ι₁ ≫ dgGluingHomTargetPreCapInputPath R C D E p q X Y =
      complexPinchedMap.{u, max (u + 1) v}
          (dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y) ≫
        dgGluingHomTargetFirstInputSection R C D E p q X Y := by
  apply dgGluingHomTargetFirstInputTriangle_hom_ext R C D E p q X Y
  · have hcap := dgGluingTriangleEvaluation_precomp (ι₁ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetPreCapInputPath R C D E p q X Y)
      (dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y)
    have hstandard := dgGluingTriangleEvaluation_precomp
      (complexPinchedMap.{u, max (u + 1) v}
        (dgGluingRightHomMap R C D (dgHomGluingBimodule R C D E p q) X Y))
      (dgGluingHomTargetFirstInputSection R C D E p q X Y)
      (dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetFirstInputSection_triangle R C D E p q X Y)
    exact hcap.trans ((dgGluingHomTargetPreCapTriangle_one_standard R C D E p q X Y).trans hstandard.symm)
  · rw [Category.assoc, dgGluingHomTargetPreCapInputPath_over R C D E p q X Y,
      ← Category.assoc, ι₁_fst, Category.id_comp, Category.assoc,
      dgGluingHomTargetFirstInputSection_input R C D E p q X Y, Category.comp_id]

lemma dgGluingHomTargetExitCapInputPath_zero :
    ι₀ ≫ dgGluingHomTargetExitCapInputPath R C D E p q X Y =
      complexPinchedMap.{u, max (u + 1) v}
          (dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y) ≫
        dgGluingHomTargetLastInputSection R C D E p q X Y := by
  apply dgGluingHomTargetLastInputTriangle_hom_ext R C D E p q X Y
  · have hcap := dgGluingTriangleEvaluation_precomp (ι₀ : P ⟶ P ⊗ Δ[1])
      (dgGluingHomTargetExitCapInputPath R C D E p q X Y)
      (dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y)
    have hstandard := dgGluingTriangleEvaluation_precomp
      (complexPinchedMap.{u, max (u + 1) v}
        (dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y))
      (dgGluingHomTargetLastInputSection R C D E p q X Y)
      (dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y)
      (dgGluingHomTargetLastInputSection_triangle R C D E p q X Y)
    exact hcap.trans ((dgGluingHomTargetExitCapTriangle_zero_standard R C D E p q X Y).trans hstandard.symm)
  · rw [Category.assoc, dgGluingHomTargetExitCapInputPath_over R C D E p q X Y,
      ← Category.assoc, ι₀_fst, Category.id_comp, Category.assoc,
      dgGluingHomTargetLastInputSection_input R C D E p q X Y, Category.comp_id]

end SerrePositivity.InfinityCategories

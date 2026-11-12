module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundaryCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundaryLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleZeroHom

/-! # dg 加群の実 fiber 境界の二未知成分

概要：実境界から未知先頭成分と N 側成分を定義し、微分式と三角形式を証明する。
方針：脚の残差と二三角形の差を逆座標へ入れ、実 Bianchi の整合式を使う。
規約：整合性を追加仮定にしない。使われ方：β3 の実 slice 境界の二単体の充填候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} {n : ℕ} (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
variable (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f))

/-- 零角へ入る実脚残差は全次数で零。 -/
lemma dgModuleFiberBoundaryRhsZero_eq_zero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero A D f b hb = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHom_eq_zero_of_closed_isZero_target (moduleZero_isZero A D) _

/-- 実残差から逆座標で定義する未知先頭成分。 -/
def dgModuleFiberBoundaryUnknownA :
    GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLift A D
    (T := ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b))
    f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb)

/-- 実境界の零角側の三角形残差を未知 N 成分として採用する。 -/
def dgModuleFiberBoundaryUnknownN :
    GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (Complex A) N)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb

/-- 未知先頭成分の実射影は M 側残差の負。 -/
lemma dgModuleFiberBoundaryUnknownA_projection :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) (dgModuleFiberBoundaryUnknownA A D f b hb)
      (add_zero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) = -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM A D f b hb :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLift_projection A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) _ _

/-- 未知先頭成分の実零ホモトピー成分は二三角形残差の差の負。 -/
lemma dgModuleFiberBoundaryUnknownA_nullHomotopy :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) (dgModuleFiberBoundaryUnknownA A D f b hb)
      (by omega) =
      -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLift_nullHomotopy A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n) _ _

/-- 実残差から得る未知先頭成分の微分は実先頭残差に等しい。 -/
lemma dgModuleFiberBoundaryUnknownA_differential :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleFiberBoundaryUnknownA A D f b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhs0 A D f b hb := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLift_differential A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM_differential A D f b hb
  · have hd : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb) =
        differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb) -
          differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb) := map_sub _ _ _
    apply hd.trans
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN_differential, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN_differential]
    abel

/-- 未知 N 成分の微分は実 N 側残差に等しい。 -/
lemma dgModuleFiberBoundaryUnknownN_differential :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleFiberBoundaryUnknownN A D f b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsN A D f b hb :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN_differential A D f b hb

/-- 左三角形の未知成分を零にすると実解はその代数式を満たす。 -/
lemma dgModuleFiberBoundaryUnknown_left_triangle :
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b)
      (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)) =
      -dgModuleFiberBoundaryUnknownN A D f b hb -
        compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
          (dgModuleFiberBoundaryUnknownA A D f b hb) (by omega) +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsMN A D f b hb := by
  rw [dgModuleFiberBoundaryUnknownA_nullHomotopy, dgModuleFiberBoundaryUnknownN]
  abel

/-- M 脚の未知成分を零にすると射影の方程式を満たす。 -/
lemma dgModuleFiberBoundaryUnknown_M_leg :
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b)
      (ForgetEnrichment.to (Complex A) M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
        (dgModuleFiberBoundaryUnknownA A D f b hb)
        (add_zero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM A D f b hb := by
  rw [dgModuleFiberBoundaryUnknownA_projection, neg_add_cancel]

/-- 零角側の脚の未知成分を零にするとその方程式を満たす。 -/
lemma dgModuleFiberBoundaryUnknown_zero_leg :
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) =
      compose A (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) 0)
        (dgModuleFiberBoundaryUnknownA A D f b hb)
        (add_zero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero A D f b hb := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, dgModuleFiberBoundaryRhsZero_eq_zero, add_zero]

/-- 零角側の三角形の未知成分を零にするとその方程式を満たす。 -/
lemma dgModuleFiberBoundaryUnknown_right_triangle :
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource A D f b)
      (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n)) =
      -dgModuleFiberBoundaryUnknownN A D f b hb +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZeroN A D f b hb := by
  exact (neg_add_cancel _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories

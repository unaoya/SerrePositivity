module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointProjectionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：一点への射が right cofinal な形状上の定値余錐は余極限である。
方針：一点上の恒等余錐を同じ形状へ制限する。
規約：元の定値余錐全体を保持する。
使われ方：有限余積の各変数を固定した全関手の sifted 保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：指定頂点への全定値余錐。
方針：join 全体の射を同じ頂点への定値射とする。
規約：元の頂点を保つ。
使われ方：定値関手の sifted 余極限保存。 -/
def constantJoinCocone (K : SSet.{u}) {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.const x : K ⟶ X) := ⟨SSet.const x, SSet.comp_const _ _⟩

/-- 概要：一点への射が right cofinal な形状上の元の全定値余錐は普遍。
方針：一点上の恒等余錐の余極限性を同じ cofinal 制限で戻す。
規約：元の定値余錐を使う。
使われ方：元の sifted 形状の定値余極限。 -/
lemma constantJoinCocone_isColimit_of_pointCofinal {K X : SSet.{u}} [Quasicategory X]
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (stdSimplex.isTerminalObj₀.from K)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (constantJoinCocone K x) := by
  let c := constantJoinCocone (Δ[0] : SSet.{u}) x
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isColimitCone_of_point_constant c x rfl
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal
    (stdSimplex.isTerminalObj₀.from K) hK c).mp hc
  have hv : (c.restrict (stdSimplex.isTerminalObj₀.from K)).val =
      (constantJoinCocone K x).val := SSet.comp_const _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hv).mp h

/-- 概要：弱可縮な形状上の指定全定値余錐は余極限。
方針：同じ一点への射の cofinality を使う。
規約：形状の充填性を要求しない。
使われ方：sifted 形状の定値成分の保存。 -/
lemma constantJoinCocone_isColimit {K X : SSet.{u}} [Quasicategory X]
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (constantJoinCocone K x) :=
  constantJoinCocone_isColimit_of_pointCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointProjection_isRightCofinal hK) x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

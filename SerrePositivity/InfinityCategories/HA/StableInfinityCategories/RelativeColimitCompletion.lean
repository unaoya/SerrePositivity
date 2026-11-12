module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies

/-! # 普遍余錐の相対的な補完
概要：既存部分で選ばれた普遍余錐を保ったまま、図式の族を補完する。
方針：普遍余錐の射影の引き戻しが trivial Kan fibration であることを使う。
規約：単なる対象ごとの選択に弱めない。使われ方：gapped 図式の cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalClosed SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：図式の族の普遍余錐を、部分上の既存の選択を固定して延長できる。
方針：図式の族上に普遍余錐の射影を引き戻し、単射に対する持ち上げを使う。
規約：各頂点での余極限の存在を明示する。使われ方：cofiber の相対的な選択。 -/
lemma exists_relative_colimitCoconeFamily {A B K C : SSet.{u}} [Quasicategory C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom K).obj C) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K C)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K C = i ≫ d)
    (hd : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm (d.app (Opposite.op ⦋0⦌) b))) :
    ∃ F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K C, i ≫ F = a ∧ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K C = d := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K C
  have htriv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd p d) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection_pullback_trivialKanFibration d hd
  let a' := pullback.lift a i ha
  have sq : CommSq a' i (pullback.snd p d) (𝟙 B) := by
    exact ⟨(pullback.lift_snd a i ha).trans (Category.comp_id i).symm⟩
  have := htriv.mem i inferInstance
  let F := sq.lift
  refine ⟨F ≫ pullback.fst p d, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sq.fac_right, Category.id_comp]

/-- 概要：普遍余錐の補完の二つの選択は、既存部分を固定する境界も相対的に持ち上げる。
方針：同じ図式の族上の引き戻し trivial Kan fibration の RLP をそのまま使う。
規約：比較のパラメーターは任意の単射。使われ方：cofiber 補完の高次の整合性。 -/
lemma colimitCoconeFamily_relative_lifting {A K C : SSet.{u}} [Quasicategory C]
    (d : A ⟶ (ihom K).obj C)
    (hd : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).symm (d.app (Opposite.op ⦋0⦌) a)))
    {U V : SSet.{u}} (j : U ⟶ V) [Mono j] :
    HasLiftingProperty j (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K C) d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection_pullback_trivialKanFibration d hd).mem j inferInstance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.colimitCoconeFamily_relative_lifting

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_relative_colimitCoconeFamily

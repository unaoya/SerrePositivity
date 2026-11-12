module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomInvertibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeApexEvaluation

/-!
概要：錐の全比較の可逆性は、元の錐頂点と底図式の比較の可逆性で判定できる。
方針：join の零単体を左右に分け、指定された全 h Fun 射に点ごとの判定を適用する。
規約：元の比較射自体を可逆にする。使われ方：模型 fiber 比較の置換単位を逆にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma joinVertex_cases {A B : SSet.{u}} (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) _⦋0⦌) :
    (∃ a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app (Opposite.op ⦋0⦌) a = x) ∨
      (∃ b, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app (Opposite.op ⦋0⦌) b = x) := by
  rcases x with ⟨l, a, b⟩
  fin_cases l
  · have ha : a = PUnit.unit := by exact @Subsingleton.elim PUnit inferInstance _ _
    subst a
    exact Or.inr ⟨b, rfl⟩
  · have hb : b = PUnit.unit := by exact @Subsingleton.elim PUnit inferInstance _ _
    subst b
    exact Or.inl ⟨a, rfl⟩

lemma coneHom_isIso_of_apex_base {B X : SSet.{u}} [Quasicategory X]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) B ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (ha : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex B)))
    (hb : IsIso (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] B) α)) : IsIso α := by
  apply functorHom_isIso_of_pointwise
  intro x
  rcases joinVertex_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have he : a = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
      apply stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      omega
    subst a
    exact ha
  · haveI := hb
    have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] B) α) b) := inferInstance
    simpa only [homPre, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp] using hi

end SerrePositivity.KST.LocalizingInvariants

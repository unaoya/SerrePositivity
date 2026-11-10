module
public import SerrePositivity.KST.ProExcision.GroupZeroMHomotopy
public import SerrePositivity.KST.ProExcision.ConjugationEquivariance
public import SerrePositivity.KST.ProExcision.LinearizedHomotopyOperations

/-!
# 群準同型の自由化と共役比較の前合成

概要：自由化の合成則を明示し、A.6 の共役比較を任意の群準同型へ前合成する。
方針：合成則を自由加群の基底で証明し、実区間ホモトピーの端点を同定する。
規約：KST Construction A.6・Lemma 4.16、非被約 C(H) と u⁻¹hu の向き。
使われ方：実 ψ と ψφ の間の m 次比較を構成する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：群準同型の自由化は準同型の合成を保つ。
方針：各単体の自由加群の基底で三つの写像を評価する。
規約：KST App. A の C(f)。使われ方：A.6 と実群準同型の前合成。 -/
lemma groupLinearizedMap_comp {T P H : Type u} [Group T] [Group P] [Group H]
    (f : T →* P) (g : P →* H) :
    groupLinearizedMap f ≫ groupLinearizedMap g = groupLinearizedMap (g.comp f) := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ g)).app n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ f)).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ (g.comp f))).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  rfl

/-- 概要：恒等群準同型の自由化は恒等写像。
方針：自由加群の基底上の恒等性を使う。
規約：KST App. A の非被約 C。使われ方：共役比較の始点の同定。 -/
lemma groupLinearizedMap_id {H : Type u} [Group H] :
    groupLinearizedMap (MonoidHom.id H) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj H))) := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ (MonoidHom.id H))).app n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  rfl

/-- 概要：群準同型とその共役の自由化の間の実 m 次ホモトピー。
方針：A.6 の実比較を前合成し、自由化の合成則で両端を同定する。
規約：KST A.6・Lemma 4.16、共役は u⁻¹f(t)u。
使われ方：ψ と ψφ の実比較。 -/
def groupConjugationMHomotopy {T H : Type u} [Group T] [Group H]
    (f : T →* H) (u : H) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap f)
      (groupLinearizedMap ((inverseConjugation u).comp f)) m := by
  let h := ((conjugationLinearizedHomotopy u).truncate m).precomp (nerveMap (SingleObj.mapHom _ _ f))
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (SingleObj.mapHom _ _ f)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (𝟭 (SingleObj H))) = groupLinearizedMap f := by
    change groupLinearizedMap f ≫ groupLinearizedMap (MonoidHom.id H) = _
    rw [groupLinearizedMap_id, Category.comp_id]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (SingleObj.mapHom _ _ f)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (conjugationFunctor u)) =
      groupLinearizedMap ((inverseConjugation u).comp f) := groupLinearizedMap_comp f (inverseConjugation u)
  refine { h := h.h, h₀ := ?_, h₁ := ?_ }
  · intro n hn
    exact (h.h₀ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hf)
  · intro n hn
    exact (h.h₁ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hg)

end SerrePositivity.KST.ProExcision

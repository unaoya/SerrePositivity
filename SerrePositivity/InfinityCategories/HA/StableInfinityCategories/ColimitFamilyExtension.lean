module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies

/-! # 指定した部分族を保つ普遍余錐の延長

概要：各頂点で余極限を持つ図式の族について、単射な部分族上で指定した普遍余錐を延長できる。
方針：普遍余錐の射影を図式の族へ引き戻し、trivial Kan fibration の持ち上げを使う。
規約：部分族と図式への制限は厳密な等式で保つ。
使われ方：S4 の接続射と cofiber 列の射で両端の普遍余錐を指定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定された単射な部分族を保って普遍余錐の族を延長する。
方針：図式の族に沿う射影の引き戻しの trivial Kan fibration 性を使う。
規約：値域は quasicategory、基底の族と部分族は任意の単体集合。
使われ方：両端を指定した余極限間の射と、高次の両立条件の構成。 -/
lemma exists_colimitCoconeFamily_extension {A₀ A K X : SSet.{u}} [Quasicategory X]
    (i : A₀ ⟶ A) [Mono i] (d : A ⟶ (ihom K).obj X)
    (hd : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (d.app (Opposite.op ⦋0⦌) a)))
    (c : A₀ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X) (hc : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X = i ≫ d) :
    ∃ f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X,
      i ≫ f = c ∧ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection_pullback_trivialKanFibration d hd
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X) d)
    i inferInstance
  let c' := pullback.lift c i hc
  have sq : CommSq c' i (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X) d) (𝟙 A) := by
    constructor
    simp only [c', pullback.lift_snd, Category.comp_id]
  refine ⟨sq.lift ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X) d, ?_, ?_⟩
  · simp only [← Category.assoc, sq.fac_left, c', pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sq.fac_right,
      Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

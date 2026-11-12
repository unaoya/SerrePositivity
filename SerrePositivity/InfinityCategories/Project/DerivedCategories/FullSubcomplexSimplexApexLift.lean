module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSubcomplexThreeSimplexLift

/-! # 始頂点と指定零面による任意次元の全部分複体への持ち上げ

概要：零面と残る始頂点が条件を満たせば、元の実単体全体を同じ台で持ち上げる。
方針：全頂点射を零頂点と正番号頂点に分け、正番号頂点は零面を経由させる。
規約：零次の面も含む。使われ方：閉細分後の高次 over 単体の実分母部分圏への回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 始頂点と指定零面の所属から、同じ実単体を任意次元で全部分複体へ上げる。 -/
def fullSubcomplexSimplexApexLift {n : ℕ} (T : X _⦋n + 1⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋n⦌)
    (h₀ : X.δ 0 T = e.val)
    (hA : P (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op T)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋n + 1⦌ := by
  refine ⟨T, ?_⟩
  intro v
  generalize hi : v.toOrderHom 0 = i
  by_cases h : i = 0
  · have he : v = SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 :=
      SimplexCategory.Hom.ext_zero_left _ _ (hi.trans h)
    rw [he]
    exact hA
  · obtain ⟨j, rfl⟩ := i.eq_succ_of_ne_zero h
    have he : v = SimplexCategory.const ⦋0⦌ ⦋n⦌ j ≫ SimplexCategory.δ (0 : Fin (n + 2)) := by
      exact SimplexCategory.Hom.ext_zero_left _ _ (by
        change v.toOrderHom 0 = j.succ
        exact hi)
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.map _ (X.δ 0 T))
    rw [h₀]
    exact e.property _

/-- 任意次元の持ち上げは元の台を厳密に保つ。 -/
lemma fullSubcomplexSimplexApexLift_val {n : ℕ} (T : X _⦋n + 1⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋n⦌)
    (h₀ : X.δ 0 T = e.val)
    (hA : P (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op T)) :
    (fullSubcomplexSimplexApexLift P T e h₀ hA).val = T := rfl

/-- 任意次元の持ち上げは指定零面を厳密に保つ。 -/
lemma fullSubcomplexSimplexApexLift_face0 {n : ℕ} (T : X _⦋n + 1⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋n⦌)
    (h₀ : X.δ 0 T = e.val)
    (hA : P (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op T)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}).δ 0
      (fullSubcomplexSimplexApexLift P T e h₀ hA) = e := Subtype.ext h₀

end SerrePositivity.InfinityCategories.Project.DerivedCategories

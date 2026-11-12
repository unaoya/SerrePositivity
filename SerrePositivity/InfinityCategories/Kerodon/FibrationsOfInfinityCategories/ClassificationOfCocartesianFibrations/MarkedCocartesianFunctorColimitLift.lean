module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorColimitFamily

/-!
概要：指定辺を各項から回収できる余極限上へ、同じ相対 Hom の族を貼り合わせる。
方針：底上の等式は全脚で検査し、指定辺の像をその辺の代表で計算する。
規約：指定辺を各項の指定辺で覆う条件を明示し、全辺の被覆と混同しない。
使われ方：元の cocartesian 辺の条件を保つ Hom の降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {J : Type v} [Category.{w} J] {T E B : SSet.{u}} (q : E ⟶ B) (D : J ⥤ Over B)
  (W : ∀ j, Set ((D.obj j).left _⦋1⦌))
  (hW : ∀ {j k} (f : j ⟶ k) e, e ∈ W j → (D.map f).left.app (Opposite.op ⦋1⦌) e ∈ W k)
  (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj j).hom (W j))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f))
  (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))

/-- 元の族の貼り合わせは、同じ底への射影を厳密に保持する。 -/
lemma markedCocartesianFamilyColimitUncurry_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc ≫ q =
      fst c.pt.left T ≫ c.pt.hom := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionTensorCocone_isColimit c hc).hom_ext
  intro j
  change ((c.ι.app j).left ▷ T) ≫ (_ ≫ q) =
    ((c.ι.app j).left ▷ T) ≫ (fst c.pt.left T ≫ c.pt.hom)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry_fac,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_projection, ← Category.assoc, whiskerRight_fst, Category.assoc]
  have hj : (c.ι.app j).left ≫ c.pt.hom = (D.obj j).hom := (c.ι.app j).w
  rw [hj]

/-- 各項の指定辺で覆われる辺は、貼り合わせた同じ族でも cocartesian に送られる。 -/
lemma markedCocartesianFamilyColimitUncurry_cocartesian (U : Set (c.pt.left _⦋1⦌))
    (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
    (x : T _⦋0⦌) (e : c.pt.left _⦋1⦌) (he : e ∈ U) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc).app (Opposite.op ⦋1⦌)
        (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  obtain ⟨j, t, ht, rfl⟩ := hU e he
  have hf := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry_fac q D W hW s hs c hc j)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc).app (Opposite.op ⦋1⦌)
    ((c.ι.app j).left.app (Opposite.op ⦋1⦌) t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = _ at hf
  rw [hf]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_cocartesian (s j) x t ht

/-- 指定辺を保持した同じ全相対 Hom の族を、余極限上へ貼り合わせる。 -/
def markedCocartesianFamilyColimitLift (U : Set (c.pt.left _⦋1⦌))
    (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q c.pt.hom U :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorCurry U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc)
    (markedCocartesianFamilyColimitUncurry_projection q D W hW s hs c hc)
    (markedCocartesianFamilyColimitUncurry_cocartesian q D W hW s hs c hc U hU)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

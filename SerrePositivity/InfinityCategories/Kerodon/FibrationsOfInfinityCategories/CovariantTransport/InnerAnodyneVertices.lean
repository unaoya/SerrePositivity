module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration

/-!
概要：inner anodyne な射の頂点における全単射性。
方針：零次成分の関数から codiscrete nerve の間の inner fibration を作り、持ち上げで逆関数を得る。
規約：元と標的の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、内ホーンによる置換後の垂直辺の条件の回収。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：inner anodyne な射は零次成分で全単射。
方針：頂点関数を codiscrete nerve の間の射へ延長し、その inner fibration に対する持ち上げを使う。
規約：頂点型が空の場合も同じ議論で扱う。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、置換した prism の各頂点を元の頂点へ戻す。 -/
lemma innerAnodyne_vertex_bijective {A B : SSet.{u}} (i : A ⟶ B)
    (hi : innerAnodyneExtensions i) : Function.Bijective (i.app (Opposite.op ⦋0⦌)) := by
  let ηA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap (fun a : A _⦋0⦌ ↦ a)
  let ηB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap (fun b : B _⦋0⦌ ↦ b)
  let q : nerve (Codiscrete (A _⦋0⦌)) ⟶ nerve (Codiscrete (B _⦋0⦌)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap (fun v ↦ i.app (Opposite.op ⦋0⦌) (nerveEquiv v).as)
  have : InnerFibration q := by
    constructor
    intro X Y j hj
    cases hj with
    | @intro n k hk0 hk1 =>
      constructor
      intro a b sq
      obtain ⟨l, hl⟩ := Quasicategory.hornFilling hk0 hk1 a
      refine CommSq.HasLift.mk' { l := l, fac_left := hl.symm, fac_right := ?_ }
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
      intro v
      have h : (horn (n + 2) k).ι ≫ (l ≫ q) = (horn (n + 2) k).ι ≫ b := by
        rw [← Category.assoc, ← hl]
        exact sq.w
      exact congrArg (fun t ↦ (nerveEquiv (t.app (Opposite.op ⦋0⦌)
        ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n k v⟩)).as) h
  have := hi q (InnerFibration.mem (q := q))
  have sq : CommSq ηA i q ηB := by
    constructor
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
    intro a
    change (nerveEquiv (q.app (Opposite.op ⦋0⦌) (ηA.app (Opposite.op ⦋0⦌) a))).as =
      (nerveEquiv (ηB.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) a))).as
    dsimp only [q, ηA, ηB]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex]
  let r : B _⦋0⦌ → A _⦋0⦌ := fun b ↦ (nerveEquiv (sq.lift.app (Opposite.op ⦋0⦌) b)).as
  have hleft (a : A _⦋0⦌) : r (i.app (Opposite.op ⦋0⦌) a) = a := by
    have h := congrArg (fun f ↦ (nerveEquiv (f.app (Opposite.op ⦋0⦌) a)).as) sq.fac_left
    change r (i.app (Opposite.op ⦋0⦌) a) =
      (nerveEquiv (ηA.app (Opposite.op ⦋0⦌) a)).as at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex] at h
    exact h
  have hright (b : B _⦋0⦌) : i.app (Opposite.op ⦋0⦌) (r b) = b := by
    have h := congrArg (fun f ↦ (nerveEquiv (f.app (Opposite.op ⦋0⦌) b)).as) sq.fac_right
    change (nerveEquiv (q.app (Opposite.op ⦋0⦌) (sq.lift.app (Opposite.op ⦋0⦌) b))).as =
      (nerveEquiv (ηB.app (Opposite.op ⦋0⦌) b)).as at h
    dsimp only [q, ηB] at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex] at h
    exact h
  exact ⟨fun a b h ↦ (hleft a).symm.trans ((congrArg r h).trans (hleft b)),
    fun b ↦ ⟨r b, hright b⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

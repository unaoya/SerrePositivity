module

public import SerrePositivity.KST.LocalizingInvariants.FinalHornContraction

/-!
概要：最終外ホーン上の正方形族は、末尾二点で pullback なら cospan の上で充填できる。
方針：欠けたセルの最後の頂点を末尾二点へ限定し、普遍正方形の終点境界充填を使う。
規約：他の頂点の正方形に普遍性を要求しない。使われ方：cartesian な辺の高次判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_finalHorn_squareFamily_extension {X : SSet.{u}} [Quasicategory X] (m : ℕ)
    (a : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    (b : (Δ[m + 2] : SSet.{u}) ⟶ (ihom (horn 2 2 : SSet.{u})).obj X)
    (ha : a ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X = (horn (m + 2) (Fin.last (m + 2))).ι ≫ b)
    (hprev : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
      (a.app (Opposite.op ⦋0⦌) (finalHornPenultimateVertex m))))
    (hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
      (a.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)))) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X,
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ F = a ∧
        F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X = b := by
  let A := horn.{u} (m + 2) (Fin.last (m + 2))
  have hA : ∀ v : (Δ[m + 2] : SSet.{u}) _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn m _
  apply exists_relative_squareFamily_of_pullback_last_vertices A hA a b ha
  intro n s hs
  let v : (A : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
    (a.app (Opposite.op ⦋0⦌) v))
  rcases finalHorn_missing_last_vertex m (n + 1) s hs with h | h
  · have hv : v = finalHornPenultimateVertex m := Subtype.ext h
    exact (congrArg (fun z : (A : SSet.{u}) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
        (a.app (Opposite.op ⦋0⦌) z))) hv).mpr hprev
  · have hv : v = finalHornLastVertex m := Subtype.ext h
    exact (congrArg (fun z : (A : SSet.{u}) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
        (a.app (Opposite.op ⦋0⦌) z))) hv).mpr hlast

end SerrePositivity.KST.LocalizingInvariants

module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
/-! 概要：三角形の全境界を元の部分単体と比較する。
方針：同じ対象族と全 cochain の異種等号を等式へ戻す。
規約：元の K と全次数を保持。使われ方：大域評価三角形の三辺の同定。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
lemma simplexData_ext_of_components {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (ho : ∀ i, s.obj i = t.obj i)
    (hh : ∀ I a b k hI ha hb hk, HEq (s.hom I a b k hI ha hb hk)
      (t.hom I a b k hI ha hb hk)) : s = t := by
  have ho' : s.obj = t.obj := funext ho
  cases s with
  | mk so sh =>
    cases t with
    | mk tobj th =>
      dsimp only at ho' hh ⊢
      cases ho'
      have he : sh = th := by
        funext I a b k hI ha hb hk
        exact eq_of_heq (hh I a b k hI ha hb hk)
      exact congrArg (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D so => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.mk so h) he

end SerrePositivity.EInfinity.ComplexLimits

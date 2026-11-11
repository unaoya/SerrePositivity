module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual

/-! # 単体残差の集合・端点・次数の輸送

概要：同じデータの残差は、等しい集合・端点・次数では異種等号で一致する。
方針：指定等式を消去し、添字証明の一意性を使う。
規約：微分後の次数も保持。使われ方：一般 Bianchi の切断残差の正規化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 等しい集合・端点・次数の残差は、微分後の次数を含めて異種等号で一致する。 -/
lemma dgSimplexResidual_heq_of_indices_degree {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {I J : Finset (Fin (n + 1))} {a b c d : Fin (n + 1)} {k l : ℤ}
    {hI : 2 ≤ I.card} {ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)}
    {hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} {hk : k = 2 - (I.card : ℤ)}
    {hJ : 2 ≤ J.card} {hc : c = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)}
    {hd : d = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)} {hl : l = 2 - (J.card : ℤ)}
    (hIJ : I = J) (hac : a = c) (hbd : b = d) (hkl : k = l) :
    HEq (s.residual I a b k hI ha hb hk) (s.residual J c d l hJ hc hd hl) := by
  subst J
  subst c
  subst d
  subst l
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories

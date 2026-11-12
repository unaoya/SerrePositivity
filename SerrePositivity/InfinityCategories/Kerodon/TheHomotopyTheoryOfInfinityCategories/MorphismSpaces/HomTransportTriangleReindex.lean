module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportTrianglePrecomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity

/-!
概要：元の輸送三角形の全 Hom 上の等式を、同じ指定四辺の共通端点へ移す。
方針：四つの端点の回収と指定値の一致を一般の貼り合わせ則に渡す。
規約：元の前合成作用と指定三角形を保持する。
使われ方：大域輸送の三角形を局所自然性の貼り合わせへ移す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の全 Hom 上の三角等式は、四端点と指定値を保持して表示変更できる。 -/
lemma HomTransportTriangleCommutesAt.reindex
    {H X₀ X₁ X₂ K : SSet.{u}}
    {a : H ⟶ X₀} {b : H ⟶ X₁} {c : H ⟶ X₂}
    {t₀₁ : X₁ ⟶ X₀} {t₁₂ : X₂ ⟶ X₁} {t₀₂ : X₂ ⟶ X₀}
    {h₀₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ t₀₁) a} {h₁₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c ≫ t₁₂) b}
    {h₀₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c ≫ t₀₂) a} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₁₂ ≫ t₀₁) t₀₂} {r : K ⟶ H}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportTriangleCommutesAt a b c t₀₁ t₁₂ t₀₂ h₀₁ h₁₂ h₀₂ e r)
    {a' b' c' t' : K ⟶ X₀}
    (ha : r ≫ (c ≫ (t₁₂ ≫ t₀₁)) = a') (hb : r ≫ (c ≫ t₀₂) = b')
    (hc : r ≫ (b ≫ t₀₁) = c') (ht : r ≫ a = t')
    (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' b') (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b' t')
    (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c') (F : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c' t')
    (hE : HEq E ((e.precomp c).precomp r)) (hD : HEq D (h₀₂.precomp r))
    (hV : HEq V ((h₁₂.postcomp t₀₁).precomp r)) (hF : HEq F (h₀₁.precomp r)) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareCommutes E D V F := by
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoSquareCommutes_reindex ha hb hc ht
    ((e.precomp c).precomp r) (h₀₂.precomp r)
    ((h₁₂.postcomp t₀₁).precomp r) (h₀₁.precomp r) E D V F h hE hD hV hF

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

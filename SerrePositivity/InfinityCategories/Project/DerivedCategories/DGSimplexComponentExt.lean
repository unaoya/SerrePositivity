module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex

/-! # 対象族が異なる dg 単体データの成分ごとの比較

概要：対象族と全斉次成分の点ごとの比較から、単体データの等式を得る。
方針：従属する射族に異種関数外延性を適用する。
規約：成分の型の輸送を省略しない。使われ方：dg 自然変換の前後合成の単体比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 対象と全斉次成分を点ごとに比較して、型を保った単体データの等式を得る。 -/
lemma dgSimplexData_ext_of_components {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n}
    (hobj : ∀ a, s.obj a = t.obj a)
    (hhom : ∀ I a b k hI ha hb hk,
      HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk)) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (funext hobj)
  apply Function.hfunext rfl
  intro I I' h
  cases h
  apply Function.hfunext rfl
  intro a a' h
  cases h
  apply Function.hfunext rfl
  intro b b' h
  cases h
  apply Function.hfunext rfl
  intro k k' h
  cases h
  apply Function.hfunext rfl
  intro hI hI' h
  cases h
  apply Function.hfunext rfl
  intro ha ha' h
  cases h
  apply Function.hfunext rfl
  intro hb hb' h
  cases h
  apply Function.hfunext rfl
  intro hk hk' h
  cases h
  exact hhom I a b k hI ha hb hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories

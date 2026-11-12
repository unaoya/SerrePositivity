module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalExtension

/-!
概要：関手 ∞ 圏の点ごとの終対象性。
方針：境界とパラメーターの直積で、指定部分の外の単体の終点を調べる。
規約：終対象性は既存の全境界の充填条件で扱う。
使われ方：HTT 5.1.2.2、Kerodon Proposition 7.1.8.10（Tag 02XK） の空図式の場合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：標準単体の境界に入らない単体の終点は最後の標準頂点。
方針：順序写像が全射なので最後の値は最大元。
規約：単体の次数は任意。
使われ方：Kerodon §7.1.8（Tag 02X8） の直積の新しいセルの終点。 -/
lemma simplexLastVertex_stdSimplex_of_notMem_boundary {n m : ℕ}
    (s : (Δ[n] : SSet.{u}) _⦋m⦌) (hs : s ∉ (boundary n).obj (Opposite.op ⦋m⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
  have hsurj : Function.Surjective (stdSimplex.asOrderHom s) := not_not.mp hs
  obtain ⟨j, hj⟩ := hsurj (Fin.last n)
  apply stdSimplex.obj₀Equiv.injective
  change s (Fin.last m) = Fin.last n
  apply le_antisymm (Fin.le_last _)
  rw [← hj]
  exact (stdSimplex.asOrderHom s).monotone (Fin.le_last j)

/-- 概要：直積の単体の終点は各成分の終点の組。
方針：Yoneda 表示と単体作用を次数零で計算する。
規約：二つの単体集合に前提は不要。
使われ方：Kerodon §7.1.8（Tag 02X8） の直積上の境界充填。 -/
lemma simplexLastVertex_prod {A B : SSet.{u}} {n : ℕ} (s : (A ⊗ B) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2) := rfl

/-- 概要：各頂点で終対象となる関手は関手 ∞ 圏でも終対象。
方針：境界の uncurry を直積上で延長し、新しい単体の終点には点ごとの終対象性を使う。
規約：この向きには標的の quasicategory 性を必要としない。
使われ方：HTT 5.1.2.2、Kerodon Corollary 7.1.8.15（Tag 02XP） の空図式の場合の双対。 -/
lemma isTerminalVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b hb
  let A : (K ⊗ (Δ[n + 1] : SSet.{u})).Subcomplex :=
    (⊤ : K.Subcomplex).prod (boundary (n + 1))
  let e : (A : SSet.{u}) ≅ K ⊗ (boundary (n + 1) : SSet.{u}) :=
    Subcomplex.prodIso ⊤ (boundary (n + 1)) ≪≫
      whiskerRightIso (Subcomplex.topIso K) (boundary (n + 1) : SSet.{u})
  let a : (A : SSet.{u}) ⟶ X := e.hom ≫ uncurry b
  have hA : ∀ v : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hblast : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ (boundary (n + 1)).obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs ⟨by trivial, h⟩
    have he₂ := simplexLastVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have ha : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩ =
        f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1) := by
      change (uncurry b).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s).1, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s).2, _⟩) = _
      rw [simplexLastVertex_prod]
      simp only [he₂]
      change (b.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _⟩).app
          (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.1) = _
      rw [hblast]
      rfl
    rw [ha]
    exact hf _
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_of_terminal_last_vertices A hA a ht
  refine ⟨curry F, ?_⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry]
  have he : e.inv ≫ A.ι = K ◁ (boundary (n + 1)).ι := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [← he, Category.assoc, hF]
  simp only [a, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

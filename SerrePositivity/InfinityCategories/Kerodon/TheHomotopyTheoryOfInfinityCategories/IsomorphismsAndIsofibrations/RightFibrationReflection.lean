module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import Mathlib.Tactic.CrossRefAttribute

/-! # 右ファイブレーションによる可逆辺の反映

概要：右ファイブレーションは可逆な像を持つ辺を可逆にする。
方針：二次の最終ホーンで逆三角形を持ち上げる。
規約：quasicategory 間の射。使われ方：D4 の slice 比較辺の可逆性。

対応節は Kerodon 4.4（Tag 01EM）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open CategoryTheory SSet SimplicialObject.Truncated
open scoped _root_.Simplicial

/-- 概要：右ファイブレーションは三角形の最後の辺と対角を固定して持ち上げる。
方針：二次の最終ホーンの二辺を貼り、右ホーンの持ち上げ性を適用する。
規約：標的の三角形と同じ三角形の上に持ち上げる。使われ方：可逆辺の反映。 -/
lemma derived_rightFibration_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌}
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂)
    (h : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₂)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₀) (q.app (Opposite.op ⦋0⦌) x₁))
    (t : SSet.Truncated.Edge.CompStruct f (g.map ((truncation 2).map q))
      (h.map ((truncation 2).map q))) :
    Nonempty (Σ f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₁,
      {t' : SSet.Truncated.Edge.CompStruct f' g h //
        q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex}) := by
  obtain ⟨a, ha₁, ha₀⟩ := horn₂₂.isPushout.exists_desc
    (SSet.yonedaEquiv.symm h.edge) (SSet.yonedaEquiv.symm g.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (h.tgt_eq.trans g.tgt_eq.symm))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (2 : Fin 3) (by decide))
  have sq : CommSq a (horn 2 2).ι q (SSet.yonedaEquiv.symm t.simplex) := by
    constructor
    apply horn₂₂.isPushout.hom_ext
    · simp only [← Category.assoc, ha₁, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₁.symm
    · simp only [← Category.assoc, ha₀, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₀.symm
  let F := sq.lift
  have hF₁ : stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm h.edge := by
    rw [← horn.ι_ι_assoc 2 1 (by decide), sq.fac_left, ha₁]
    rfl
  have hF₀ : stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm g.edge := by
    rw [← horn.ι_ι_assoc 2 0 (by decide), sq.fac_left, ha₀]
    rfl
  let s := SSet.yonedaEquiv F
  have h₁ : X.δ 1 s = h.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁]
    exact SSet.yonedaEquiv.apply_symm_apply h.edge
  have h₀ : X.δ 0 s = g.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀]
    exact SSet.yonedaEquiv.apply_symm_apply g.edge
  have hsrc : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) s) = x₀ := by
    have he : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) s) =
        X.δ (1 : Fin 2) (X.δ (1 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₁]
    exact h.src_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) = x₁ := by
    have he : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) =
        X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [he, h₀]
    exact g.src_eq
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₁ :=
    ⟨X.δ 2 s, hsrc, htgt⟩
  refine ⟨f', ⟨⟨s, rfl, h₀, h₁⟩, ?_⟩⟩
  change q.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv sq.lift) = _
  rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

/-- 概要：右ファイブレーションは辺の可逆性を反映する。
方針：逆三角形を二回持ち上げ、二つの片側逆から両側逆を得る。
規約：両単体的集合は quasicategory。使われ方：slice の錐の同型不変性。 -/
@[kerodon 019K]
lemma derived_rightFibration_reflects_invertibleEdge {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map q))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have split {a b : X _⦋0⦌}
      (g : SSet.Truncated.Edge (X := (truncation 2).obj X) a b)
      (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (g.map ((truncation 2).map q))) :
      ∃ f : SSet.Truncated.Edge (X := (truncation 2).obj X) b a,
        SSet.Truncated.HomotopyCategory.homMk f ≫
          SSet.Truncated.HomotopyCategory.homMk g = 𝟙 _ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f.map ((truncation 2).map q)) := by
    obtain ⟨f, t₁, t₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.nonempty_inverse hg
    have t : SSet.Truncated.Edge.CompStruct f (g.map ((truncation 2).map q))
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj X) b).map ((truncation 2).map q)) := by
      simpa only [SSet.Truncated.Edge.map_id] using t₂
    obtain ⟨f', t', ht'⟩ := derived_rightFibration_liftCompStruct q g
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) b) f t
    have hf' : f'.map ((truncation 2).map q) = f := by
      apply SSet.Truncated.Edge.ext
      change q.app (Opposite.op ⦋1⦌) f'.edge = f.edge
      rw [← t'.d₂]
      calc
        _ = Y.δ 2 (q.app (Opposite.op ⦋2⦌) t'.simplex) :=
          ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 2).op) t'.simplex
        _ = f.edge := by rw [ht']; exact t.d₂
    refine ⟨f', ?_, ?_⟩
    · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t'
    · rw [hf']
      refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map q)), ?_, ?_⟩⟩
      · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₂
      · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t₁
  obtain ⟨f, hf, hqf⟩ := split e he
  obtain ⟨k, hk, _⟩ := split f hqf
  have heq : SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk k := by
    calc
      _ = (SSet.Truncated.HomotopyCategory.homMk k ≫
          SSet.Truncated.HomotopyCategory.homMk f) ≫
            SSet.Truncated.HomotopyCategory.homMk e := by rw [hk, Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory.homMk k ≫
          (SSet.Truncated.HomotopyCategory.homMk f ≫
            SSet.Truncated.HomotopyCategory.homMk e) := Category.assoc _ _ _
      _ = SSet.Truncated.HomotopyCategory.homMk k := by rw [hf, Category.comp_id]
  exact ⟨⟨SSet.Truncated.HomotopyCategory.homMk f, by rw [heq]; exact hk, hf⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

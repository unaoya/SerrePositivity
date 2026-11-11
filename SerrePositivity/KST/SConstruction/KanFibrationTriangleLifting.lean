module
public import SerrePositivity.KST.SConstruction.RelativeFamilyRectification
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 指定した基底三角形と二辺を保つ Kan fibration の充填
概要：外側の逆三角形と内側の合成三角形を、元の二辺と基底二単体を固定して持ち上げる。
方針：二次ホーンの pushout 表示と元の Kan fibration のホーン RLP を使う。
規約：欠けた辺と実三角形だけを選び、基底への射影は厳密に保持する。
使われ方：パラメータ境界で指定した逆・合成三角形の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Kan fibration は外側三角形の前辺と対角を固定して、欠けた辺を厳密に持ち上げる。 -/
lemma exists_kanFibration_liftOuterTriangle {E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    {x₀ x₁ x₂ : E _⦋0⦌} (f : E.Edge x₀ x₁) (h : E.Edge x₀ x₂)
    (g : B.Edge (q.app _ x₁) (q.app _ x₂))
    (t : SSet.Edge.CompStruct (f.map q) g (h.map q)) :
    ∃ g' : E.Edge x₁ x₂, ∃ t' : SSet.Edge.CompStruct f g' h,
      q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex ∧
        q.app (Opposite.op ⦋1⦌) g'.edge = g.edge := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q := ⟨by
    intro A X i hi
    cases hi with
    | @intro n i hn =>
      exact ((SSet.modelCategoryQuillen.fibration_iff q).mp inferInstance) _ (horn_ι_mem_J _ _)⟩
  obtain ⟨g', t', ht'⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftCompStruct q f.toTruncated h.toTruncated g.toTruncated t.toTruncated).some
  refine ⟨SSet.Edge.ofTruncated g', SSet.Edge.CompStruct.ofTruncated t', ht', ?_⟩
  have he := congrArg (B.δ (0 : Fin 3)) ht'
  rw [← SSet.δ_naturality_apply] at he
  have ht₀ : E.δ (0 : Fin 3) t'.simplex = g'.edge := t'.d₀
  exact (congrArg (q.app (Opposite.op ⦋1⦌)) ht₀).symm.trans (he.trans t.d₀)

/-- Kan fibration は指定した二つの前後の辺を保ち、基底の合成三角形を厳密に持ち上げる。 -/
lemma exists_kanFibration_liftCompositionTriangle {E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    {x₀ x₁ x₂ : E _⦋0⦌} (f : E.Edge x₀ x₁) (g : E.Edge x₁ x₂)
    (h : B.Edge (q.app _ x₀) (q.app _ x₂))
    (t : SSet.Edge.CompStruct (f.map q) (g.map q) h) :
    ∃ h' : E.Edge x₀ x₂, ∃ t' : SSet.Edge.CompStruct f g h',
      q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex ∧
        q.app (Opposite.op ⦋1⦌) h'.edge = h.edge := by
  obtain ⟨a, ha₂, ha₀⟩ := horn₂₁.isPushout.exists_desc
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) (by
      rw [SSet.Edge.δ_zero_yonedaEquiv_symm, SSet.Edge.δ_one_yonedaEquiv_symm])
  let : HasLiftingProperty (horn 2 1).ι q :=
    ((SSet.modelCategoryQuillen.fibration_iff q).mp inferInstance) _ (horn_ι_mem_J 2 1)
  have sq : CommSq a (horn 2 1).ι q (SSet.yonedaEquiv.symm t.simplex) := by
    constructor
    apply horn₂₁.isPushout.hom_ext
    · simp only [← Category.assoc, ha₂, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₂.symm
    · simp only [← Category.assoc, ha₀, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact t.d₀.symm
  let s := SSet.yonedaEquiv sq.lift
  have hs₂ : E.δ 2 s = f.edge := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc 1 2 (by decide),
      sq.fac_left, ha₂, Equiv.apply_symm_apply]
  have hs₀ : E.δ 0 s = g.edge := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc 1 0 (by decide),
      sq.fac_left, ha₀, Equiv.apply_symm_apply]
  have hsrc : E.δ (1 : Fin 2) (E.δ (1 : Fin 3) s) = x₀ := by
    have he : E.δ (1 : Fin 2) (E.δ (1 : Fin 3) s) =
        E.δ (1 : Fin 2) (E.δ (2 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ => E.map α.op s)
      decide
    rw [he, hs₂]
    exact f.src_eq
  have htgt : E.δ (0 : Fin 2) (E.δ (1 : Fin 3) s) = x₂ := by
    have he : E.δ (0 : Fin 2) (E.δ (1 : Fin 3) s) =
        E.δ (0 : Fin 2) (E.δ (0 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ => E.map α.op s)
      decide
    rw [he, hs₀]
    exact g.tgt_eq
  let h' : E.Edge x₀ x₂ := ⟨E.δ 1 s, hsrc, htgt⟩
  have hs : q.app (Opposite.op ⦋2⦌) s = t.simplex := by
    rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  refine ⟨h', ⟨s, hs₂, hs₀, rfl⟩, hs, ?_⟩
  have he := congrArg (B.δ (1 : Fin 3)) hs
  rw [← SSet.δ_naturality_apply, t.d₁] at he
  exact he

end SerrePositivity.KST.SConstruction

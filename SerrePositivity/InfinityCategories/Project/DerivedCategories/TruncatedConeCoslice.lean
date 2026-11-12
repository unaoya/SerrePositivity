module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedConeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice

/-! # 切断錐データから実 coslice への切断写像

概要：指定次数の錐単体を、共通 apex の実 coslice の単体と自然変換へ移す。
方針：点と標準単体の join 同型と全順序写像への錐の自然性を使う。
規約：零面は元の図式のまま保つ。使われ方：有限図式からの実 join 錐の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet Opposite
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ}

/-- 錐単体を同じ apex からの実 coslice 単体へ移す。 -/
def TruncatedJoinConeData.cosliceSimplex (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderVertex C.apex) _⦋n⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (C.simplex n hn σ), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inl_vertex]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    simp only [SSet.yonedaEquiv_symm_app, Equiv.apply_symm_apply]
    have hv : stdSimplex.objEquiv (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2))) =
        SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
      apply SimplexCategory.Hom.ext_zero_left
      rfl
    rw [hv]
    exact C.first_vertex n hn σ⟩

/-- 各次数の実 coslice 単体は切断単体圏上で自然。 -/
def TruncatedJoinConeData.cosliceMap (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) :
    (truncation N).obj K ⟶ (truncation N).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderVertex C.apex) where
  app a := ↾fun σ => C.cosliceSimplex a.unop.obj.len a.unop.property σ
  naturality a b α := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso b.unop.obj.len).hom ≫
        SSet.yonedaEquiv.symm (C.simplex b.unop.obj.len b.unop.property (K.map α.unop.hom.op σ)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.map α.unop.hom) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso a.unop.obj.len).hom ≫
          SSet.yonedaEquiv.symm (C.simplex a.unop.obj.len a.unop.property σ))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc]
    congr 1
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact (C.naturality b.unop.property a.unop.property α.unop.hom σ).symm

/-- 実 coslice 単体の射影は同じ元の図式単体。 -/
lemma TruncatedJoinConeData.cosliceSimplex_projection (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm C.apex)).app _
      (C.cosliceSimplex n hn σ) = f.app _ σ := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (C.simplex n hn σ))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr]
  have h := SSet.yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin (n + 2)))
    (SSet.yonedaEquiv.symm (C.simplex n hn σ))
  exact h.symm.trans (by rw [Equiv.apply_symm_apply]; exact C.face_zero n hn σ)

/-- coslice への切断写像は元の図式の射影上の厳密な持ち上げ。 -/
lemma TruncatedJoinConeData.cosliceMap_projection (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) :
    C.cosliceMap ≫ (truncation N).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm C.apex)) =
      (truncation N).map f := by
  ext a σ
  exact C.cosliceSimplex_projection a.unop.obj.len a.unop.property σ

end SerrePositivity.InfinityCategories.Project.DerivedCategories

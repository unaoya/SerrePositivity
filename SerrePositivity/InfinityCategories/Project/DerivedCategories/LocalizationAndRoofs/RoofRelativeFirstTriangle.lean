module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.RoofFirstHornPrism

/-! # 部分パラメーターを固定した外三角形の充填

概要：部分パラメーター上の三角形と全パラメーター上の二辺を同時に延長する。
方針：零番外ホーンと部分パラメーターの pushout-product の左 anodyne 性を使う。
規約：底の三角形と全指定境界を厳密に保つ。使われ方：実屋根の相対輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 左ファイブレーションの外三角形は、部分係数上の充填を固定して延長できる。 -/
lemma roofLeftFibration_relativeFirstTriangle {K L E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (j : K ⟶ L) [Mono j]
    (f g : L ⊗ Δ[1] ⟶ E)
    (h : (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ f =
      (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ g)
    (U : K ⊗ Δ[2] ⟶ E) (b : L ⊗ Δ[2] ⟶ B)
    (hf : (j ▷ Δ[1]) ≫ f = (K ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ U)
    (hg : (j ▷ Δ[1]) ≫ g = (K ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ U)
    (hfp : f ≫ p = (L ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ b)
    (hgp : g ≫ p = (L ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ b)
    (hUp : U ≫ p = (j ▷ Δ[2]) ≫ b) :
    ∃ W : L ⊗ Δ[2] ⟶ E,
      (L ◁ (SSet.stdSimplex.δ (2 : Fin 3))) ≫ W = f ∧
      (L ◁ (SSet.stdSimplex.δ (1 : Fin 3))) ≫ W = g ∧
      (j ▷ Δ[2]) ≫ W = U ∧ W ≫ p = b := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism f g h
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) j (horn 2 0).ι
  have hw : (j ▷ Λ[2, 0]) ≫ H = (K ◁ (horn 2 0).ι) ≫ U := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_isPushout K).hom_ext
    · rw [← Category.assoc, whisker_exchange, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge01, hf, ← Category.assoc,
        ← whiskerLeft_comp, horn.ι_ι]
    · rw [← Category.assoc, whisker_exchange, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge02, hg, ← Category.assoc,
        ← whiskerLeft_comp, horn.ι_ι]
  let w := sq.isPushout.desc H U hw
  have hHp : H ≫ p = (L ◁ (horn 2 0).ι) ≫ b := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_isPushout L).hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge01, hfp,
        ← Category.assoc, ← whiskerLeft_comp, horn.ι_ι]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge02, hgp,
        ← Category.assoc, ← whiskerLeft_comp, horn.ι_ι]
  have hwp : w ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hHp
    · rw [← Category.assoc, sq.isPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      exact hUp
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (horn 2 (0 : Fin 3)).ι := by
    intro X Y q hq
    exact hq _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin 3) (by decide))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_right j (horn 2 0).ι hi sq p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
  let c : CommSq w sq.ι p b := ⟨hwp⟩
  have hl : sq.inl ≫ sq.ι = L ◁ (horn 2 0).ι := sq.inl_ι
  have hr : sq.inr ≫ sq.ι = j ▷ Δ[2] := sq.inr_ι
  have hH : (L ◁ (horn 2 0).ι) ≫ c.lift = H := by
    rw [← hl, Category.assoc, c.fac_left]
    exact sq.isPushout.inl_desc _ _ _
  have hU : (j ▷ Δ[2]) ≫ c.lift = U := by
    rw [← hr, Category.assoc, c.fac_left]
    exact sq.isPushout.inr_desc _ _ _
  refine ⟨c.lift, ?_, ?_, hU, c.fac_right⟩
  · have hh := congrArg (fun k => (L ◁ horn₂₀.ι₀₁) ≫ k) hH
    rw [← Category.assoc, ← whiskerLeft_comp, horn.ι_ι,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge01] at hh
    exact hh
  · have hh := congrArg (fun k => (L ◁ horn₂₀.ι₀₂) ≫ k) hH
    rw [← Category.assoc, ← whiskerLeft_comp, horn.ι_ι,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstHornPrism_edge02] at hh
    exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories

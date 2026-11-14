module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationComparison

/-! # 貼り合わせ比較の恒等成分の消去

概要：外側から右面への比較の右下は恒等であり、恒等と同じ Arrow の成分を合成から消せる。
方針：固定頂点の道を計算し、一般の圏では Arrow の端点の等号を消去する。
規約：最初の二補題は任意の圏。使われ方：八面体の第二比較の三成分の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：右因子が恒等射と同じ Arrow なら、合成の Arrow は左因子の Arrow と同じ。
方針：恒等射との Arrow の等号で二端点と射を置き換える。
規約：任意の圏で端点表示の違いを許す。使われ方：第二比較の始点成分の計算。 -/
lemma stableArrow_comp_of_right_identity {C : Type*} [Category* C] {x y z w : C}
    (f : x ⟶ y) (g : y ⟶ z) (h : Arrow.mk g = Arrow.mk (𝟙 w)) :
    Arrow.mk (f ≫ g) = Arrow.mk f := by
  obtain ⟨hy, hz, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst w
  subst z
  simp only [eqToHom_refl, Category.comp_id] at hg
  subst g
  rw [Category.comp_id]

/-- 概要：左因子が恒等射と同じ Arrow なら、合成の Arrow は右因子の Arrow と同じ。
方針：恒等射との Arrow の等号で二端点と射を置き換える。
規約：任意の圏。使われ方：第二比較の終点成分の計算。 -/
lemma stableArrow_comp_of_left_identity {C : Type*} [Category* C] {x y z w : C}
    (f : x ⟶ y) (g : y ⟶ z) (h : Arrow.mk f = Arrow.mk (𝟙 w)) :
    Arrow.mk (f ≫ g) = Arrow.mk g := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst w
  subst y
  simp only [eqToHom_refl, Category.comp_id] at hf
  subst f
  rw [Category.id_comp]

/-- 概要：外側から右面への比較形状は右下の頂点を固定する。
方針：右列の横座標が二であり、時間に依存しないことを計算する。
規約：形状の厳密な等号。使われ方：第二比較の中間成分の恒等性。 -/
lemma pastingOuterToRightShape_middle :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightShape = snd Δ[0] Δ[1] ≫
        SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) 1 0) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：外側から右面への比較は右下で定値の道を与える。
方針：形状の固定式を長方形で評価する。
規約：値域への追加仮定なし。使われ方：中間成分の評価。 -/
lemma pastingOuterToRightHomotopy_middle {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F).h =
        snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 0) := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightShape ≫ F) = _
  rw [← Category.assoc, pastingOuterToRightShape_middle, Category.assoc, SSet.const_comp]
  rfl

/-- 概要：外側から右面への比較の右下成分は恒等射。
方針：固定した頂点の自然変換成分をホモトピー圏の評価と比較する。
規約：値域への充填性の仮定なし。使われ方：八面体の中間対象の恒等性。 -/
lemma pastingOuterToRightHom_middle {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 0).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom F) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 0) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F).h
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 0) (pastingOuterToRightHomotopy_middle F)
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F) _).trans h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

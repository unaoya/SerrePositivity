module

public import SerrePositivity.InfinityCategories.F1B.Diagrams.OppositeHomotopyInvolution
public import SerrePositivity.InfinityCategories.F1B.KanExtension.TransportOppositeReflection
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightCylinder

/-!
概要：指定右 Kan 変換を保持して左 Kan 条件へ双対化する。
方針：左条件の反転による判定に二重反転の異種等式を合成する。
規約：変換の存在だけでなく、元の指定変換そのものを戻す。
使われ方：左 Kan の大域的 Hom 普遍性を右 Kan へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：右 Kan 条件は対象と図式と指定変換の異種等式で移送できる。
方針：対象の等式を消去し、図式とホモトピーの等式へ帰着する。
規約：変換は raw な円柱射の異種等式で指定する。
使われ方：二重反転した右 Kan 条件の正規化。 -/
lemma kanIsRightKanExtension_iff_of_heq_data
    {K K' C C' D D' : SSet.{u}} (hK : K = K') (hC : C = C') (hD : D = D')
    (δ : K ⟶ C) (δ' : K' ⟶ C') (F₀ : K ⟶ D) (F₀' : K' ⟶ D')
    (F : C ⟶ D) (F' : C' ⟶ D')
    (α : SSet.Homotopy (δ ≫ F) F₀) (α' : SSet.Homotopy (δ' ≫ F') F₀')
    (hδ : HEq δ δ') (h₀ : HEq F₀ F₀') (hF : HEq F F') (hα : HEq α.h α'.h) :
    IsRightKanExtension δ F₀ F α ↔ IsRightKanExtension δ' F₀' F' α' := by
  cases hK
  cases hC
  cases hD
  have hd := eq_of_heq hδ
  have h0 := eq_of_heq h₀
  have hf := eq_of_heq hF
  subst δ'
  subst F₀'
  subst F'
  have ha : α = α' := SSet.RelativeMorphism.Homotopy.ext (eq_of_heq hα)
  subst α'
  rfl

/-- 概要：指定右 Kan 変換の反転は左 Kan 変換である。
方針：左条件の反転判定へ元の右条件を二重反転で移送して渡す。
規約：標的 D のみ quasicategory とする。
使われ方：右 Kan 拡張の Hom 普遍性の双対化。 -/
lemma kanIsRightKanExtension_opposite {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀)
    (hα : IsRightKanExtension δ F₀ F α) :
    IsLeftKanExtension (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opFunctor.map F) (rightKanOppositeTransformation δ F₀ F α) := by
  apply (kanIsLeftKanExtension_iff_opposite _ _ _ _).2
  apply (kanIsRightKanExtension_iff_of_heq_data
    (SerrePositivity.InfinityCategories.F1B.opposite_opposite_eq K) (SerrePositivity.InfinityCategories.F1B.opposite_opposite_eq C) (SerrePositivity.InfinityCategories.F1B.opposite_opposite_eq D)
    _ δ _ F₀ _ F _ α (SerrePositivity.InfinityCategories.F1B.opposite_map_map_heq δ) (SerrePositivity.InfinityCategories.F1B.opposite_map_map_heq F₀)
    (SerrePositivity.InfinityCategories.F1B.opposite_map_map_heq F) ?_).2 hα
  exact SerrePositivity.InfinityCategories.F1B.homotopyOpposite_double_h_heq α

end SerrePositivity.InfinityCategories.F1B

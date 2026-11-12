module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.EdgeTrianglePrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensorRight

/-!
概要：coslice の辺の全族を読む、左に点を置く実三角形の prism。
方針：Δ[0]⋆Δ[1]≅Δ[2] と既存の右因子の直積比較を使う。
規約：辺形状のみ。使われ方：表現可能値の比較と標準後合成の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：coslice の prism の二点への制限は、元の左区間比較の prism。
方針：join の切断位置と二つの成分を照合する。
規約：既存の区間比較を保持。使われ方：表現可能値の比較の両端。 -/
lemma coslicePointPrism_eq (A : SSet.{u}) :
    ((joinStdSimplexIso 0 0).inv ▷ A) ≫ joinTensorRight Δ[0] Δ[0] A ≫
      joinMap (𝟙 Δ[0]) (snd Δ[0] A) = leftMappingSpacePrism A := by
  symm
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  change (joinCylinderMap Δ[0] A).app (Opposite.op ⦋n⦌)
    (((SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) :
      (Δ[1] : SSet.{u}) ⊗ A ⟶ (Δ[0] : SSet.{u})).app _ (t, a), t), a) = _
  rw [joinCylinderMap_app]
  refine TheSliceAndJoinConstructions.Join.Simplex.ext _ _ rfl ?_ ?_
  · have hp (k : ℕ) : Subsingleton
        (TheSliceAndJoinConstructions.Join.augObj (Δ[0] : SSet.{u}) k) := by
      cases k with
      | zero =>
        change Subsingleton PUnit
        infer_instance
      | succ k =>
        change Subsingleton ((Δ[0] : SSet.{u}) _⦋k⦌)
        exact ⟨fun u v => by
          apply stdSimplex.ext
          intro i
          apply Fin.ext
          omega⟩
    exact (hp _).elim _ _
  · symm
    exact Join.augTensorEquiv_symm_augHomSnd Δ[0] A _ _ _

/-- 概要：点と辺の join を、辺の全パラメータ族への錐として読む prism。
方針：標準三角形の join 表示に既存の直積比較を合成する。
規約：区間は第一因子。使われ方：coslice の輸送の実三角形。 -/
def cosliceEdgeTrianglePrism (A : SSet.{u}) :
    (Δ[2] : SSet.{u}) ⊗ A ⟶ join Δ[0] ((Δ[1] : SSet.{u}) ⊗ A) :=
  ((joinStdSimplexIso 0 1).inv ▷ A) ≫ joinTensorRight Δ[0] Δ[1] A

/-- 概要：右因子の直積比較は、点から辺への写像と可換。
方針：join の切断位置と成分を計算する。
規約：全パラメータを保持。使われ方：二つの側面の式。 -/
lemma cosliceEdgeTriangle_tensor_point (A : SSet.{u}) (i : Fin 2) :
    (joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) ▷ A) ≫
      joinTensorRight Δ[0] Δ[1] A =
    joinTensorRight Δ[0] Δ[0] A ≫
      joinMap (𝟙 Δ[0]) (stdSimplex.δ i ▷ A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  rcases s with ⟨l, b, c⟩
  change Join.tensorRightSimplex Δ[0] Δ[1] A n
    ((joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i)).app (Opposite.op ⦋n⦌)
      ⟨l, b, c⟩) a =
    (joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i ▷ A)).app (Opposite.op ⦋n⦌)
      (Join.tensorRightSimplex Δ[0] Δ[0] A n ⟨l, b, c⟩ a)
  dsimp [joinMap, Join.tensorRightSimplex]
  simp only [TheSliceAndJoinConstructions.Join.augHom_id,
    Join.augTensorEquiv_symm_augHomLeft]

/-- 概要：二つの側面は二点の同じ prism の端点への包含。
方針：辺形状の既存の join の面と直積比較の自然性を使う。
規約：i=1 が第一面、i=0 が長辺。使われ方：coslice の全族の三面。 -/
lemma cosliceEdgeTrianglePrism_side (A : SSet.{u}) (i : Fin 2) :
    (stdSimplex.δ i.succ ▷ A) ≫ cosliceEdgeTrianglePrism A =
      ((joinStdSimplexIso 0 0).inv ▷ A) ≫ joinTensorRight Δ[0] Δ[0] A ≫
        joinMap (𝟙 Δ[0]) (stdSimplex.δ i ▷ A) := by
  have h : stdSimplex.δ i.succ ≫ (joinStdSimplexIso.{u} 0 1).inv =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) := by
    apply (cancel_mono (joinStdSimplexIso.{u} 0 1).hom).mp
    simp only [Category.assoc, edgeTriangleJoin_face, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  unfold cosliceEdgeTrianglePrism
  rw [← Category.assoc, ← comp_whiskerRight, h, comp_whiskerRight, Category.assoc,
    cosliceEdgeTriangle_tensor_point]

/-- 概要：第二面は辺の全族そのものへの右包含。
方針：標準三角形の辺と join の右包含の一致を使う。
規約：面番号は 0。使われ方：同じ指定辺の定値族。 -/
lemma cosliceEdgeTrianglePrism_edge (A : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ cosliceEdgeTrianglePrism A =
      joinInr Δ[0] ((Δ[1] : SSet.{u}) ⊗ A) := by
  have he : joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have h : stdSimplex.δ (0 : Fin 3) ≫ (joinStdSimplexIso.{u} 0 1).inv =
      joinInr (Δ[0] : SSet.{u}) Δ[1] := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold cosliceEdgeTrianglePrism
  rw [← Category.assoc, ← comp_whiskerRight, h, joinTensorRight_inr]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

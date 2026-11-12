module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions

/-!
概要：辺形状の錐の全族を実三角形へ読むための prism と三面。
方針：Δ[0]⋆Δ[1]≅Δ[2] と既存の join/直積比較を使う。
規約：形状は Δ[1] のみ。パラメータ A は任意。
使われ方：G8 の共通 span の三面の照合。
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

/-- 概要：辺への錐を読む三角形の全パラメータ prism。
方針：二点と辺の join の標準単体表示を使う。
規約：辺形状のみ。使われ方：共通 span の実三角形。 -/
def edgeTrianglePrism (A : SSet.{u}) : A ⊗ (Δ[2] : SSet.{u}) ⟶ join A Δ[1] :=
  (A ◁ (joinStdSimplexIso 0 1).inv) ≫ joinTensorLeft A Δ[0] Δ[1] ≫
    joinMap (fst A Δ[0]) (𝟙 Δ[1])

/-- 概要：二点の join 上の直積比較は、元の右 pinched/interval prism と同じ射。
方針：join の切断位置と二つの成分を計算する。
規約：全パラメータを保持。使われ方：第一面の独立した比較。 -/
lemma edgePointPrism_eq (A : SSet.{u}) :
    (β_ A (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism A =
      (A ◁ (joinStdSimplexIso 0 0).inv) ≫ joinTensorLeft A Δ[0] Δ[0] ≫
        joinMap (fst A Δ[0]) (𝟙 Δ[0]) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  change (joinCylinderMap A Δ[0]).app (Opposite.op ⦋n⦌)
      ((a, t), (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) :
        A ⊗ (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u})).app _ (a, t)) = _
  rw [joinCylinderMap_app]
  let s := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  refine TheSliceAndJoinConstructions.Join.Simplex.ext _ _ rfl ?_ ?_
  · symm
    exact Join.augTensorEquiv_symm_augHomFst A Δ[0] _ _ _
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

/-- 概要：点を辺の一端へ写す join の面は、対応する標準三角形の面。
方針：両因子の Yoneda 単体を照合する。
規約：二つの側面のみ。使われ方：三角形 prism の面。 -/
lemma edgeTriangleJoin_face (i : Fin 2) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) ≫
        (joinStdSimplexIso 0 1).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ i.succ := by
  apply join_hom_to_stdSimplex_ext
  all_goals
    apply SSet.yonedaEquiv.injective
    fin_cases i <;> decide

/-- 概要：join/直積比較は、右の点を辺の一端へ写す射と可換。
方針：切断位置と各成分を計算する。
規約：パラメータは任意。使われ方：二つの側面の制限。 -/
lemma edgeTriangle_tensor_point (A : SSet.{u}) (i : Fin 2) :
    (A ◁ joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i)) ≫
        joinTensorLeft A Δ[0] Δ[1] =
      joinTensorLeft A Δ[0] Δ[0] ≫ joinMap (𝟙 (A ⊗ Δ[0])) (stdSimplex.δ i) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  rcases s with ⟨l, b, c⟩
  change Join.tensorLeftSimplex A Δ[0] Δ[1] n a
      ((joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i)).app (Opposite.op ⦋n⦌) ⟨l, b, c⟩) =
    (joinMap (𝟙 (A ⊗ Δ[0])) (stdSimplex.δ i)).app (Opposite.op ⦋n⦌)
      (Join.tensorLeftSimplex A Δ[0] Δ[0] n a ⟨l, b, c⟩)
  dsimp [joinMap, Join.tensorLeftSimplex]
  simp only [TheSliceAndJoinConstructions.Join.augHom_id]

/-- 概要：三角形の第一面と長辺は、それぞれ同じ右 prism の二端への写像。
方針：join の面の式、右の点の自然性、二点上の prism の同定を使う。
規約：i=1 が第一面、i=0 が長辺。使われ方：元の Hom と β_native の区間像。 -/
lemma edgeTrianglePrism_side (A : SSet.{u}) (i : Fin 2) :
    (A ◁ stdSimplex.δ i.succ) ≫ edgeTrianglePrism A =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism A ≫
        joinMap (𝟙 A) (stdSimplex.δ i) := by
  have h : stdSimplex.δ i.succ ≫ (joinStdSimplexIso.{u} 0 1).inv =
      (joinStdSimplexIso 0 0).inv ≫
        joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) := by
    apply (cancel_mono (joinStdSimplexIso.{u} 0 1).hom).mp
    simp only [Category.assoc, edgeTriangleJoin_face, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  unfold edgeTrianglePrism
  rw [← Category.assoc, ← whiskerLeft_comp, h, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i)),
    edgeTriangle_tensor_point]
  conv_rhs => rw [← Category.assoc, edgePointPrism_eq]
  simp only [Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：辺上に固定された第二面は、パラメータを忘れた右包含。
方針：標準三角形の面と join の右包含を照合する。
規約：面番号は 0。使われ方：指定辺の定値族。 -/
lemma edgeTrianglePrism_edge (A : SSet.{u}) :
    (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ edgeTrianglePrism A =
      snd A (Δ[1] : SSet.{u}) ≫ joinInr A Δ[1] := by
  have he : joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have h : stdSimplex.δ (0 : Fin 3) ≫ (joinStdSimplexIso.{u} 0 1).inv =
      joinInr (Δ[0] : SSet.{u}) Δ[1] := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold edgeTrianglePrism
  rw [← Category.assoc, ← whiskerLeft_comp, h]
  rw [← Category.assoc, joinTensorLeft_inr, Category.assoc, joinInr_joinMap,
    Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

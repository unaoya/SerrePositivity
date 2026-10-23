module

public import SerrePositivity.InfinityCategories.F1B.KanCylinderMaximumAction
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinBaseProjection
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：写像円柱の全体から右端への自然な変形。
方針：円柱の最大値による変形と固定された右端を、直積で移した pushout で貼る。
規約：右端は変形中も厳密に固定される。
使われ方：相対 join の右端への制限の Hom 対応を得る準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：写像円柱の円柱部分を右端へ送り、右端を固定する変形の射。
方針：直積が保存する pushout で円柱部分の最大値作用と右端の定値族を貼る。
規約：変形の時刻は最後の因子。
使われ方：写像円柱の右端を右随伴として表す単位の構成。 -/
def kanMappingCylinderContraction {K C : SSet.{u}} (p : K ⟶ C) :
    pushout (prismEndpoint 1 K) p ⊗ (Δ[1] : SSet.{u}) ⟶ pushout (prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (prismEndpoint 1 K) p).map (tensorRight (Δ[1] : SSet.{u}))).desc
    (kanCylinderMaximumAction K ≫ pushout.inl (prismEndpoint 1 K) p)
    (fst C (Δ[1] : SSet.{u}) ≫ pushout.inr (prismEndpoint 1 K) p) (by
      change (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
        (kanCylinderMaximumAction K ≫ pushout.inl (prismEndpoint 1 K) p) =
          (p ▷ (Δ[1] : SSet.{u})) ≫ (fst C Δ[1] ≫ pushout.inr (prismEndpoint 1 K) p)
      rw [← Category.assoc, kanCylinderMaximumAction_fixed_one, Category.assoc, pushout.condition]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ pushout.inr (prismEndpoint 1 K) p) (whiskerRight_fst p Δ[1]).symm)

/-- 概要：変形の円柱部分への制限は最大値による変形。
方針：直積した pushout の第一包含への制限を使う。
規約：右端との貼り合わせ後も元の円柱部分を厳密に保つ。
使われ方：変形の両端点の計算。 -/
lemma kanMappingCylinderContraction_inl {K C : SSet.{u}} (p : K ⟶ C) :
    (pushout.inl (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
      kanMappingCylinderContraction p =
        kanCylinderMaximumAction K ≫ pushout.inl (prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).inl_desc _ _ _

/-- 概要：変形の右端への制限は右端の恒等族。
方針：直積した pushout の第二包含への制限を使う。
規約：変形の時刻によらず右端は固定する。
使われ方：単位を右端へ制限した三角恒等式。 -/
lemma kanMappingCylinderContraction_inr {K C : SSet.{u}} (p : K ⟶ C) :
    (pushout.inr (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
      kanMappingCylinderContraction p = fst C (Δ[1] : SSet.{u}) ≫
        pushout.inr (prismEndpoint 1 K) p :=
  ((IsPushout.of_hasPushout (prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).inr_desc _ _ _

/-- 概要：写像円柱の変形の始点は恒等射。
方針：pushout の両部分で変形の零端点を計算する。
規約：円柱全体の厳密な恒等射。
使われ方：右端への変形を単位のホモトピーとする。 -/
lemma kanMappingCylinderContraction_zero {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.ι₀ ≫ kanMappingCylinderContraction p = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [← SSet.ι₀_comp_assoc, kanMappingCylinderContraction_inl, ← Category.assoc,
      kanCylinderMaximumAction_zero, Category.id_comp, Category.comp_id]
  · rw [← SSet.ι₀_comp_assoc, kanMappingCylinderContraction_inr, ← Category.assoc]
    simp

/-- 概要：写像円柱の変形の終点は底への射影と右包含の合成。
方針：円柱部分は一端点へ畳み、右端では恒等射となることを確認する。
規約：係数の底への射影を用いる。
使われ方：右端への制限の大域的 Hom 対応。 -/
lemma kanMappingCylinderContraction_one {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.ι₁ ≫ kanMappingCylinderContraction p =
      mappingCylinderBaseProjection p ≫ pushout.inr (prismEndpoint 1 K) p := by
  apply pushout.hom_ext
  · rw [← SSet.ι₁_comp_assoc, kanMappingCylinderContraction_inl, ← Category.assoc,
      kanCylinderMaximumAction_one, Category.assoc, pushout.condition]
    rw [reassoc_of% (mappingCylinderBaseProjection_inl p)]
  · rw [← SSet.ι₁_comp_assoc, kanMappingCylinderContraction_inr, ← Category.assoc,
      ← Category.assoc, mappingCylinderBaseProjection_inr, Category.id_comp]
    simp

/-- 概要：写像円柱の変形は係数の底への射影を固定する。
方針：直積した pushout の両部分で係数を忘れないことを確認する。
規約：変形の時刻には依存しない等式。
使われ方：右端の包含と底への射影の単位の三角恒等式。 -/
lemma kanMappingCylinderContraction_baseProjection {K C : SSet.{u}} (p : K ⟶ C) :
    kanMappingCylinderContraction p ≫ mappingCylinderBaseProjection p =
      fst (pushout (prismEndpoint 1 K) p) (Δ[1] : SSet.{u}) ≫ mappingCylinderBaseProjection p := by
  apply ((IsPushout.of_hasPushout (prismEndpoint 1 K) p).map
    (tensorRight (Δ[1] : SSet.{u}))).hom_ext
  · change (pushout.inl (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (kanMappingCylinderContraction p ≫ mappingCylinderBaseProjection p) =
      (pushout.inl (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (fst (pushout (prismEndpoint 1 K) p) Δ[1] ≫ mappingCylinderBaseProjection p)
    rw [reassoc_of% (kanMappingCylinderContraction_inl p),
      mappingCylinderBaseProjection_inl]
    rw [reassoc_of% (whiskerRight_fst (pushout.inl (prismEndpoint 1 K) p) Δ[1]),
      mappingCylinderBaseProjection_inl]
    rw [← Category.assoc, kanCylinderMaximumAction_snd, Category.assoc]
  · change (pushout.inr (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (kanMappingCylinderContraction p ≫ mappingCylinderBaseProjection p) =
      (pushout.inr (prismEndpoint 1 K) p ▷ (Δ[1] : SSet.{u})) ≫
        (fst (pushout (prismEndpoint 1 K) p) Δ[1] ≫ mappingCylinderBaseProjection p)
    rw [reassoc_of% (kanMappingCylinderContraction_inr p),
      mappingCylinderBaseProjection_inr, Category.comp_id]
    rw [reassoc_of% (whiskerRight_fst (pushout.inr (prismEndpoint 1 K) p) Δ[1]),
      mappingCylinderBaseProjection_inr, Category.comp_id]

/-- 概要：写像円柱の恒等射から右端への射影の合成への自然なホモトピー。
方針：貼り合わせた変形の射に両端点の計算を添える。
規約：quasicategory 性を要求しない。
使われ方：相対 join の右端への Hom 対応の単位の代表。 -/
def kanMappingCylinderUnit {K C : SSet.{u}} (p : K ⟶ C) :
    SSet.Homotopy (𝟙 (pushout (prismEndpoint 1 K) p))
      (mappingCylinderBaseProjection p ≫ pushout.inr (prismEndpoint 1 K) p) where
  h := kanMappingCylinderContraction p
  h₀ := kanMappingCylinderContraction_zero p
  h₁ := kanMappingCylinderContraction_one p
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.F1B

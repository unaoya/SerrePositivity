module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionMono

/-! # 頂点の条件による充満 dg 部分圏への持ち上げ

概要：全ての頂点の対象が性質 P を満たす dg nerve への写像は、充満 dg 部分圏へ持ち上がる。
方針：自然性で各単体の全対象を頂点から回収し、range_inclusion と像への同型を使う。
規約：HA Construction 1.3.1.6。使われ方：標準 fiber の充填を充満部分圏へ制限する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 概要：写像の全零単体の対象が P を満たすなら、その全像は P 上の充満部分単体集合に含まれる。
方針：各単体の頂点を定値順序写像で取り出し、写像の自然性を評価する。
規約：HA Construction 1.3.1.6。使われ方：充満 dg 部分圏の包含の像へ写像を制限する。 -/
lemma range_le_fullOnObjects_of_vertices {Z : SSet.{max u v}} (F : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hvertices : ∀ z : Z _⦋0⦌, P ((F.app _ z).obj 0)) :
    SSet.Subcomplex.range F ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullOnObjects A D P := by
  rintro ⟨⟨n⟩⟩ s ⟨z, rfl⟩ i
  have H := congrArg (fun q => (q z).obj 0)
    (F.naturality (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op)
  simp only [CategoryTheory.comp_apply] at H
  exact H ▸ hvertices (Z.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op z)

/-- 概要：頂点の対象が全て P を持つ写像を充満 dg 部分圏の nerve へ持ち上げる。
方針：像を range_inclusion で包含の像へ制限し、toRange の逆同型を合成する。
規約：HA Construction 1.3.1.6。使われ方：充填写像や標準四角形を部分圏の内部に作る。 -/
def fullInclusionLift {Z : SSet.{max u v}} (F : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hvertices : ∀ z : Z _⦋0⦌, P ((F.app _ z).obj 0)) : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P) :=
  SSet.Subcomplex.lift F (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.range_inclusion A D P]
    exact range_le_fullOnObjects_of_vertices A D P F hvertices) ≫
      inv (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)))

/-- 概要：持ち上げた写像の包含による像は元の写像。
方針：toRange と包含の分解、像への同型の逆、部分複体の lift の制限公式を使う。
規約：HA Construction 1.3.1.6。使われ方：境界・固定図式との一致を包含の単射性で検証する。 -/
lemma fullInclusionLift_comp {Z : SSet.{max u v}} (F : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hvertices : ∀ z : Z _⦋0⦌, P ((F.app _ z).obj 0)) :
    fullInclusionLift A D P F hvertices ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P) = F := by
  have hh : inv (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P) =
      (SSet.Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))).ι := by
    calc
      _ = inv (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))) ≫
          (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) ≫
            (SSet.Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))).ι) :=
        congrArg (fun q => inv (SSet.Subcomplex.toRange
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))) ≫ q)
          (SSet.Subcomplex.toRange_ι (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))).symm
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  unfold fullInclusionLift
  rw [Category.assoc, hh, SSet.Subcomplex.lift_ι]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

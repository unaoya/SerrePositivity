module

public import Mathlib.CategoryTheory.Iso

/-!
概要：三つの合成関係から二つの内部同型を消去する式。
方針：各関係を順方向の射の等式にして同型の逆を消去する。
規約：任意の通常の圏の同型を扱う。
使われ方：三角形の比較円柱の三つの四面の関係をまとめる。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：三つの四面の合成則は内部同型を消去した円柱の合成則を与える。
方針：元の三つの等式で置き換えて、各逆同型との合成を消す。
規約：外側の指定同型の値を保持する。
使われ方：脚の指定比較同型の自然性の証明。 -/
lemma prismIso_cancel {C : Type u} [Category.{v} C]
    {W H₁ I₀ I₁ H₀ T₁ M T₀ : C}
    (a : W ≅ H₁) (top : H₁ ≅ T₁) (i₀ : W ≅ I₀) (uf : I₀ ≅ T₁)
    (i₁ : W ≅ I₁) (ug : I₁ ≅ M) (lf : I₀ ≅ M)
    (lg : I₁ ≅ T₀) (lh : W ≅ H₀) (bottom : H₀ ≅ T₀)
    (h₀ : a ≪≫ top = i₀ ≪≫ uf) (h₁ : i₁ ≪≫ ug = i₀ ≪≫ lf)
    (h₂ : i₁ ≪≫ lg = lh ≪≫ bottom) :
    bottom ≪≫ lg.symm ≪≫ ug ≪≫ lf.symm ≪≫ uf = lh.symm ≪≫ a ≪≫ top := by
  have h0 := congrArg Iso.hom h₀
  have h1 := congrArg Iso.hom h₁
  have h2 := congrArg Iso.hom h₂
  simp only [Iso.trans_hom] at h0 h1 h2
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = lh.inv ≫ (lh.hom ≫ bottom.hom) ≫ lg.inv ≫ ug.hom ≫ lf.inv ≫ uf.hom := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = lh.inv ≫ (i₁.hom ≫ lg.hom) ≫ lg.inv ≫ ug.hom ≫ lf.inv ≫ uf.hom := by rw [← h2]
    _ = lh.inv ≫ (i₁.hom ≫ ug.hom) ≫ lf.inv ≫ uf.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = lh.inv ≫ (i₀.hom ≫ lf.hom) ≫ lf.inv ≫ uf.hom := by rw [h1]
    _ = lh.inv ≫ (i₀.hom ≫ uf.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [← h0]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

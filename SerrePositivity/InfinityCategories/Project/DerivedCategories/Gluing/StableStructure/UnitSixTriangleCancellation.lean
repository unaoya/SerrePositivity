module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitSpanHexagonReduction
/-! # 六片の実合成関係から単位面を消去する

概要：六つの二単体の合成関係から、二つの単位閉路を消去して係数六角形を得る。
方針：共有対角を照合し、係数辺とその始側辺の実同型だけを相殺する。
規約：合成関係と単位閉路の零性を明示入力に分け、辺の代表を変更しない。
使われ方：実六片の二単体から正本の指定境界充填へ進む。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory
lemma dgGluingUnitSixTriangle_cancel {E : Type u} [Category.{v} E]
    {a b c d e : E} (k : d ≅ b) (q : d ≅ c)
    (df : a ⟶ b) (dl : d ⟶ e) (r : a ⟶ c) (s : c ⟶ b) (l : c ⟶ e)
    (ur : b ⟶ b) (ul : d ⟶ d) (v : a ⟶ b) (w : d ⟶ e) (bridge : a ⟶ e)
    (h0 : df ≫ ur = v) (h1 : r ≫ s = v)
    (h2 : ul ≫ dl = w) (h3 : q.hom ≫ l = w)
    (h4 : q.hom ≫ s = k.hom) (h5 : r ≫ l = bridge)
    (hr : ur = 𝟙 b) (hl : ul = 𝟙 d) : df ≫ k.inv ≫ dl = bridge := by
  have hf : df = r ≫ s := by simpa only [hr, Category.comp_id] using h0.trans h1.symm
  have hd : dl = q.hom ≫ l := by
    simpa only [hl, Category.id_comp] using h2.trans h3.symm
  have hs : s = q.inv ≫ k.hom := by
    rw [← h4, q.inv_hom_id_assoc]
  rw [hf, hd, hs]
  simpa only [Category.assoc, k.hom_inv_id_assoc, q.inv_hom_id_assoc] using h5
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

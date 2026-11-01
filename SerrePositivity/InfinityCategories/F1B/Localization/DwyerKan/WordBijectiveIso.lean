module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordFactorization

/-!
# 元の列の全単射から語の同型を回収する

概要：列番号の全単射である元の語の射は同型である。
方針：元の単射への恒等射の因子分解を逆射にし、元の単射性で他方の恒等式を得る。
規約：向きを保つ元の射自身について IsIso を証明する。
使われ方：欠けた列を全て挿入した後の帰納法の基底。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma isIso_of_bijective {a b : Word} (f : a ⟶ b) (hf : Function.Bijective f.orderHom) :
    IsIso f := by
  let g := factorEmbedding f hf.1 (𝟙 b) (by
    intro j _
    exact hf.2 j)
  refine ⟨⟨g.val, ?_, g.property⟩⟩
  apply hom_ext
  intro i
  apply hf.1
  have h : (f ≫ g.val) ≫ f = f := by rw [Category.assoc, g.property, Category.comp_id]
  exact congrArg (fun k => k.orderHom i) h

end SerrePositivity.EInfinity.Hammock.Word

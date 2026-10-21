module
public import SerrePositivity.KST.SConstruction.CofiberFamilyActionLaws

/-! # 全パラメータ自然性四角形と商射の合成
概要：元の族に可換な商射の後合成は、区間を保つ全族自然性を保存する。
方針：商射の回収式と元の作用の自然性を whisker の合成則でつなぐ。
規約：任意の単体的パラメータ。使われ方：巨大な Perf の型を展開しない組み立て比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の区間作用の可換式は、同じ商射を後合成した区間作用にも成立する。 -/
lemma parameterizedQuotientSquare {I X X' Y Y' Q Q' P : SSet.{u}}
    (f : I ⊗ X ⟶ Y) (f' : I ⊗ X' ⟶ Y') (s : X ⊗ P ⟶ X') (t : Y ⊗ P ⟶ Y')
    (q : Y ⟶ Q) (q' : Y' ⟶ Q') (tQ : Q ⊗ P ⟶ Q')
    (hn : (f ▷ P) ≫ t = (α_ I X P).hom ≫ (I ◁ s) ≫ f')
    (hq : (q ▷ P) ≫ tQ = t ≫ q') :
    ((f ≫ q) ▷ P) ≫ tQ = (α_ I X P).hom ≫ (I ◁ s) ≫ f' ≫ q' := by
  rw [comp_whiskerRight, Category.assoc, hq, ← Category.assoc, hn, Category.assoc]
  rw [Category.assoc]

end SerrePositivity.KST.SConstruction

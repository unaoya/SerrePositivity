module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TensorExchangeCoherence

/-!
概要：三つの左因子の交換の二経路は、同じ右側の因子を保って厳密に一致する。
方針：braiding の Yang–Baxter 等式を右テンソルし、結合子の coherence で表示をそろえる。
規約：閉構造不要。使われ方：二重 mapping 列のパラメータ交換の構造条件。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.HomTensorStrength
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 最初の三因子の交換は Yang–Baxter 等式を満たし、右側の因子は同じまま保つ。 -/
lemma exchange_braid (A K S T : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K (S ⊗ T)).hom ≫ K ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A S T).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange K S (A ⊗ T)).hom =
    A ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange K S T).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A S (K ⊗ T)).hom ≫
      S ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K T).hom := by
  have h := congrArg (fun f =>
    (A ◁ (α_ K S T).inv ≫ (α_ A (K ⊗ S) T).inv) ≫ f ▷ T ≫
      ((α_ S (K ⊗ A) T).hom ≫ S ◁ (α_ K A T).hom)) (BraidedCategory.yang_baxter A K S)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor] at ⊢
  convert h using 1 <;> monoidal

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_braid := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_braid

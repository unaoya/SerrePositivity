module

public import SerrePositivity.KST.ProExcision.KoszulGraded
public import SerrePositivity.HomologicalAlgebra.CochainTensorScalarCone

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 全テンソルと既存 Koszul 構成の比較

概要：濾過の全体である Koszul 複体との全テンソルを既存の反復錐模型へ比較する。
方針：テンソルとスカラー作用の cone の可換性を列長について反復する。
規約：元の列の正則性・係数複体の平坦性は不要。
使われ方：KST Lemma 4.10 のスペクトル系列の収束先を実際の Koszul 商へ接続する。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：スカラー cone との全テンソルは、全テンソル上のスカラー cone。
方針：テンソルと cone の同型にスカラー倍写像の線形性を合わせる。
規約：任意のスカラー a。使われ方：KST Lemma 4.10 の反復 Koszul 模型の比較。 -/
def scalarConeTensorIso (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : R) :
    cochainTensor ((scalarConeFunctor a).obj P) K ≅
      (scalarConeFunctor a).obj (cochainTensor P K) :=
  cochainTensorConeLeft (smulId a P) K ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        rw [smulId, cochainTensorMap_smul_left, cochainTensorMap_id]
        rfl))

/-- 概要：Koszul 複体との全テンソルは既存の係数付き反復錐模型と同型。
方針：空列では単位律、列を延ばす段階ではスカラー cone 比較を使う。
規約：複体の有界性や平坦性は不要。使われ方：KST Lemma 4.10 の収束先の同定。 -/
def totalKoszulTensorIso : ∀ {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    cochainTensor (koszulComplex z) K ≅ koszulComplexOn z K
  | 0, _, K => cochainTensorLeftUnitor K
  | e + 1, z, K =>
    scalarConeTensorIso (koszulComplex (Fin.init z)) K (z (Fin.last e)) ≪≫
      (scalarConeFunctor (z (Fin.last e))).mapIso (totalKoszulTensorIso (Fin.init z) K)

end SerrePositivity.KST.ProExcision

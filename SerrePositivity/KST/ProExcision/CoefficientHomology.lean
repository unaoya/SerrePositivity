module

public import SerrePositivity.KST.ProExcision.KoszulFirstPage

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 平坦係数間の射とホモロジー比較

概要：平坦な左テンソルのホモロジー比較は、係数加群の射にも自然である。
方針：短複体のホモロジー比較の自然変換に関する公式を使う。
規約：二つの係数加群はそれぞれ平坦。
使われ方：KST Lemma 4.10 の Koszul 微分の係数ホモロジーへの移送。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：平坦な左テンソルのホモロジー比較は、二つの係数関手の間の自然変換と可換。
方針：短複体の比較公式をホモロジー同型の正射で前合成する。
規約：ホモロジー次数 q と係数自然変換を明示する。
使われ方：KST Lemma 4.10 の係数射のホモロジー計算。 -/
theorem flatLeftTensorHomologyIso_coefficient
    (M N : ModuleCat.{u} R) [Module.Flat R M] [Module.Flat R N]
    (τ : tensorLeft M ⟶ tensorLeft N)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    homologyMap ((τ.mapHomologicalComplex (.up ℤ)).app K) q ≫
      (flatLeftTensorHomologyIso N q).hom.app K =
      (flatLeftTensorHomologyIso M q).hom.app K ≫ τ.app (K.homology q) := by
  let : (tensorLeft M).PreservesHomology := Functor.preservesHomologyOfExact _
  let : (tensorLeft N).PreservesHomology := Functor.preservesHomologyOfExact _
  have h := congrArg (fun f ↦ ((K.sc q).mapHomologyIso (tensorLeft M)).hom ≫ f)
    (NatTrans.app_homology τ (K.sc q))
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
  exact h.symm

/-- 概要：平坦係数の射をテンソルしてからホモロジーを取ると、ホモロジーのテンソル上の同じ射になる。
方針：モノイダル構造が与える係数自然変換を一般比較へ適用する。
規約：係数射の像や単射性に仮定はない。使われ方：KST Lemma 4.10 の Koszul 係数微分。 -/
theorem flatLeftTensorHomologyIso_map
    {M N : ModuleCat.{u} R} [Module.Flat R M] [Module.Flat R N] (f : M ⟶ N)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    homologyMap ((((curriedTensor (ModuleCat.{u} R)).map f).mapHomologicalComplex (.up ℤ)).app K) q ≫
      (flatLeftTensorHomologyIso N q).hom.app K =
      (flatLeftTensorHomologyIso M q).hom.app K ≫ (f ▷ K.homology q) :=
  flatLeftTensorHomologyIso_coefficient M N ((curriedTensor (ModuleCat.{u} R)).map f) K q

end SerrePositivity.KST.ProExcision

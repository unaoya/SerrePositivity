module

public import SerrePositivity.HomologicalAlgebra.ComplexLimits.ExtendTruncationHomNaturality

/-!
# 実 smart 切断と負次数延長の比較の標的自然性

概要：元の truncLE' の射は、同じ延長・切断同型・包含と可換。
方針：延長の像と像の外で成分を計算し、元の切断包含の自然性を使う。
規約：誘導された射を別の随伴の選択で置き換えない。
使われ方：正規化 Hom と実 DK Hom の前後作用との整合。
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

private lemma extendXOpIso_unop_naturality {K L : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ L) (i : Option ℕ) :
    extend.mapX f i ≫ (extend.XOpIso L i).hom.unop =
      (extend.XOpIso K i).hom.unop ≫
        (extend.mapX ((opFunctor (ModuleCat A) (.down ℕ)).map f.op) i).unop := by
  cases i <;> simp [extend.mapX, extend.XOpIso, extend.X]

lemma truncLEIso_inv_naturality {K L : Complex A} (f : K ⟶ L)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE] :
    extendMap (truncLE'Map f e) e ≫ (L.truncLEIso e).inv =
      (K.truncLEIso e).inv ≫ truncLEMap f e := by
  apply HomologicalComplex.Hom.ext
  funext i
  change extend.mapX (truncLE'Map f e) (e.r i) ≫
      (extend.XOpIso (L.truncLE' e) (e.r i)).hom.unop =
    (extend.XOpIso (K.truncLE' e) (e.r i)).hom.unop ≫
      (extend.mapX ((opFunctor (ModuleCat A) (.down ℕ)).map
        (truncLE'Map f e).op) (e.r i)).unop
  exact extendXOpIso_unop_naturality (truncLE'Map f e) (e.r i)

lemma extendTruncationHomEquiv_postcomp (P : ChainComplex (ModuleCat.{u} A) ℕ)
    {K L : Complex A} (f : P.extend (ComplexShape.embeddingUpIntLE 0) ⟶ K) (g : K ⟶ L) :
    extendTruncationHomEquiv P L (f ≫ g) =
      extendTruncationHomEquiv P K f ≫ truncLE'Map g (ComplexShape.embeddingUpIntLE 0) := by
  apply (extendTruncationHomEquiv P L).symm.injective
  rw [Equiv.symm_apply_apply, extendTruncationHomEquiv_symm_apply, extendMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (extendMap (truncLE'Map g _) _) (L.truncLEIso _).inv,
    truncLEIso_inv_naturality, Category.assoc]
  simp only [CochainComplex.ιTruncLE]
  rw [HomologicalComplex.ιTruncLE_naturality]
  have h := (extendTruncationHomEquiv P K).symm_apply_apply f
  rw [extendTruncationHomEquiv_symm_apply] at h
  simpa only [Category.assoc, CochainComplex.ιTruncLE] using
    (congrArg (fun t => t ≫ g) h).symm

end SerrePositivity.EInfinity.ComplexLimits

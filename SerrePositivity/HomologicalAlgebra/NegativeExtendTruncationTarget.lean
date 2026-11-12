module
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationNaturality

/-!
概要：図式圏にも使える延長・切断 Hom 同値の標的変数への自然性。
方針：指定切断同型と延長射の可換性を成分で示し、逆 Hom 同値で比較する。
規約：標的の元の複体射を truncLE'Map へ送る。別の包含を選び直さない。
使われ方：HA 1.2.4、G10 の係数図式の射を保つ Dold–Kan 比較。
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem extendXOpIso_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L) (i : Option ℕ) :
    extend.mapX f i ≫ (extend.XOpIso L i).hom.unop =
      (extend.XOpIso K i).hom.unop ≫
        (extend.mapX ((opFunctor C (.down ℕ)).map f.op) i).unop := by
  cases i <;> simp [extend.mapX, extend.XOpIso, extend.X]

/-- 指定切断同型の逆射は元の複体射に自然。 -/
theorem negativeTruncationIso_inv_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE] :
    extendMap (truncLE'Map f e) e ≫ (L.truncLEIso e).inv =
      (K.truncLEIso e).inv ≫ truncLEMap f e := by
  apply HomologicalComplex.Hom.ext
  funext i
  change extend.mapX (truncLE'Map f e) (e.r i) ≫
      (extend.XOpIso (L.truncLE' e) (e.r i)).hom.unop =
    (extend.XOpIso (K.truncLE' e) (e.r i)).hom.unop ≫
      (extend.mapX ((opFunctor C (.down ℕ)).map (truncLE'Map f e).op) (e.r i)).unop
  exact extendXOpIso_naturality (truncLE'Map f e) (e.r i)

/-- 同定済み埋め込みでの Hom 同値は元の複体射の後合成を保つ。 -/
theorem extendTruncationHomEquivOfEmbedding_postcomp
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (P : ChainComplex C ℕ)
    {K L : CochainComplex C ℤ} (f : P.extend e ⟶ K) (g : K ⟶ L) :
    extendTruncationHomEquivOfEmbedding e he P L (f ≫ g) =
      extendTruncationHomEquivOfEmbedding e he P K f ≫
        truncLE'Map g (ComplexShape.embeddingUpIntLE 0) := by
  subst e
  change zeroExtendTruncationHomEquiv P L _ = zeroExtendTruncationHomEquiv P K f ≫ _
  apply (zeroExtendTruncationHomEquiv P L).symm.injective
  rw [Equiv.symm_apply_apply, zeroExtendTruncationHomEquiv_symm, extendMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (extendMap (truncLE'Map g _) _) (L.truncLEIso _).inv,
    negativeTruncationIso_inv_naturality, Category.assoc]
  simp only [CochainComplex.ιTruncLE]
  rw [HomologicalComplex.ιTruncLE_naturality]
  have h := (zeroExtendTruncationHomEquiv P K).symm_apply_apply f
  rw [zeroExtendTruncationHomEquiv_symm] at h
  simpa only [Category.assoc, CochainComplex.ιTruncLE] using
    (congrArg (fun t => t ≫ g) h).symm

/-- 負次数延長の Hom 同値は元の全標的射に自然。 -/
theorem negativeExtendTruncationHomEquiv_postcomp (P : ChainComplex C ℕ)
    {K L : CochainComplex C ℤ} (f : P.extend ComplexShape.embeddingDownNat ⟶ K) (g : K ⟶ L) :
    negativeExtendTruncationHomEquiv P L (f ≫ g) =
      negativeExtendTruncationHomEquiv P K f ≫ truncLE'Map g (ComplexShape.embeddingUpIntLE 0) :=
  extendTruncationHomEquivOfEmbedding_postcomp _ negativeEmbedding_eq P f g

end SerrePositivity.HomologicalAlgebra

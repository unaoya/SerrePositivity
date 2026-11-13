module
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncation
/-!
概要：指定切断mateは図式圏と点ごとの同じHom随伴を保つ。
方針：右随伴の一意性の指定単位則をHom随伴の公式へ適用する。
規約：IS-W2 B02の係数移送の同じ証明分割。指定mateを取り替えない。
使われ方：HA 1.2.4、元の正規化重みHomの点ごとの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]
/-- 同じ指定切断mateを後合成すると元のHom随伴の値が一致する。 -/
theorem truncationExchangeMate_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    (diagramTruncationAdjunction J C).homEquiv K X f ≫
        (truncationExchangeMate J C).hom.app X =
      (pointwiseTruncationAdjunction J C).homEquiv K X f := by
  dsimp only [truncationExchangeMate]
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc]
  erw [NatTrans.naturality]
  erw [← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]
/-- 図式側の調整したHom随伴は元のHom随伴と指定交換余単位で表される。 -/
theorem diagramTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    (diagramTruncationAdjunction J C).homEquiv K
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f) =
    (negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f ≫
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C)).map
        ((functorComplexExchangeCounitIso J C (.up ℤ)).inv.app H) := by
  dsimp only [diagramTruncationAdjunction]
  erw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [Iso.hom_inv_id_app_assoc, Adjunction.comp_homEquiv]
  change (negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv _ _
    ((functorComplexExchangeCounitIso J C (.up ℤ)).inv.app _ ≫
      (functorToComplexOfFunctors J C (.up ℤ)).map
        (complexOfFunctorsToFunctorToComplex.map f)) = _
  rw [← Adjunction.homEquiv_naturality_right]
  exact congrArg ((negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K _)
    ((functorComplexExchangeCounitIso J C (.up ℤ)).inv.naturality f).symm
/-- 点ごとの随伴を成分交換から戻すと同じ図式Hom随伴になる。 -/
theorem pointwiseTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    complexOfFunctorsToFunctorToComplex.map
        ((pointwiseTruncationAdjunction J C).homEquiv K X f) ≫
      (functorComplexExchangeUnitIso J C (.down ℕ)).inv.app
        (X ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor C) =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) X f := by
  dsimp only [pointwiseTruncationAdjunction]
  rw [Adjunction.comp_homEquiv]
  let g := (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
    (complexOfFunctorsToFunctorToComplex.obj K) X f
  change complexOfFunctorsToFunctorToComplex.map
    ((functorComplexExchangeCounitIso J C (.down ℕ)).inv.app K ≫
      (functorToComplexOfFunctors J C (.down ℕ)).map g) ≫
      (functorComplexExchangeUnitIso J C (.down ℕ)).inv.app _ = g
  apply NatTrans.ext
  funext j
  apply HomologicalComplex.Hom.ext
  funext n
  change (𝟙 _ ≫ (g.app j).f n) ≫ 𝟙 _ = (g.app j).f n
  simp only [Category.id_comp, Category.comp_id]
/-- 同じ指定点ごとの切断同型は元の零延長Hom随伴を保つ。 -/
theorem pointwiseTruncationIso_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    complexOfFunctorsToFunctorToComplex.map
        ((negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f) ≫
      (pointwiseTruncationIso J C).hom.app H =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f) := by
  let X := complexOfFunctorsToFunctorToComplex.obj H
  let f' := (pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
    complexOfFunctorsToFunctorToComplex.map f
  have h := truncationExchangeMate_homEquiv J C K X f'
  rw [diagramTruncationHomEquiv_exchange] at h
  have h' := congrArg (fun t => complexOfFunctorsToFunctorToComplex.map t ≫
    (functorComplexExchangeUnitIso J C (.down ℕ)).inv.app
      (X ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor C)) h
  rw [pointwiseTruncationHomEquiv_exchange] at h'
  simpa [pointwiseTruncationIso, functorComplexExchangeEquivalence,
    Functor.map_comp, Category.assoc, X, f'] using h'
end SerrePositivity.HomologicalAlgebra

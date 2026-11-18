module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomProjectedEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendTruncationHomInclusion

/-!
概要：指定自由負次数鎖の逆随伴をMooreの逆随伴と同じ切断包含に分ける。
方針：既存合成随伴の逆射則と二つの延長Hom同値の逆射を比較する。
規約：零次数のcyclesと指定負次数埋め込みを保持する既存構成の合成則。
使われ方：HA 1.2.4、IS-W2 B02の全AW成分の複体への輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 指定自由負次数鎖の逆随伴は同じMoore逆随伴と延長逆随伴の合成。 -/
theorem freeNegativeChainsAdjunction_symm_moore (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv
        ((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ ModuleCat.free A)) H).symm
        (((freeMooreChainsAdjunction (R := A)).homEquiv S
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f) := by
  simp only [freeNegativeChainsAdjunction, freeMooreChainsAdjunction,
    Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  rfl

/-- 同じ延長Hom同値の逆射は元の延長射と切断包含の合成。 -/
theorem negativeExtendTruncationAdjunction_symm_inclusion
    (L : ChainComplex (ModuleCat A) ℕ) (H : Complex A)
    (g : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv L H).symm g =
      extendMap g ComplexShape.embeddingDownNat ≫
        _root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H := by
  have h (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
      (he : e = ComplexShape.embeddingUpIntLE 0) :
      (extendTruncationHomEquivOfEmbedding e he L H).symm g =
        extendMap g e ≫ _root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A e he H := by
    subst e
    rfl
  simp only [negativeExtendTruncationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    negativeExtendTruncationHomEquiv]
  exact h _ _

/-- 指定自由負次数鎖の逆射は元のMoore逆射を延長して包含したもの。 -/
theorem freeNegativeChainsAdjunction_symm_inclusion (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      extendMap (((freeMooreChainsAdjunction (R := A)).homEquiv S
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f)
          ComplexShape.embeddingDownNat ≫
        _root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H := by
  rw [freeNegativeChainsAdjunction_symm_moore,
    negativeExtendTruncationAdjunction_symm_inclusion]

/-- 同じ逆随伴の射影生成元は、同じΓのMoore射影と余単位で評価できる。 -/
theorem freeNegativeChainsAdjunction_symm_generator_eval (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction A).homEquiv S H).symm f).f (-(n : ℤ))
      (freeNegativeGenerator S n s) =
      (((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H).f (-(n : ℤ)))
        (((DoldKan.PInftyToNormalizedMooreComplex
          (Abelian.DoldKan.Γ.obj (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))).f n ≫
          (Abelian.DoldKan.equivalence.counitIso.hom.app
            (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).f n)
              (f.app (Opposite.op ⦋n⦌) s)) := by
  let L := (normalizedMooreComplex (ModuleCat A)).obj (S ⋙ ModuleCat.free A)
  let g : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0) :=
    ((freeMooreChainsAdjunction (R := A)).homEquiv S
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f
  have he : (L.extendXIso ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (extendMap g ComplexShape.embeddingDownNat).f (-(n : ℤ)) =
      g.f n ≫ ((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv := by
    have h := extendMap_f g ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl
    have h' := congrArg (fun t => (L.extendXIso ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl).inv ≫ t) h
    simp only [Iso.inv_hom_id_assoc] at h'
    exact h'

  rw [freeNegativeChainsAdjunction_symm_inclusion]
  change ((L.extendXIso ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (extendMap g ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫
      (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H).f (-(n : ℤ)))
      ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free A)).f n
        (ModuleCat.freeMk s)) = _
  rw [← Category.assoc, he]
  simp only [ModuleCat.comp_apply]
  exact congrArg (fun t =>
    (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero H).f (-(n : ℤ))
      (((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv t))
    (normalizedFreeHomEquiv_symm_projected_eval S
      (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) f n s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

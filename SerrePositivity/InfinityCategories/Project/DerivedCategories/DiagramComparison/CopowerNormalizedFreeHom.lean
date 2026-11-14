module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction
public import SerrePositivity.HomologicalAlgebra.CopowerUnitFree
public import SerrePositivity.HomologicalAlgebra.CopowerUnitHomDiagram
public import SerrePositivity.HomologicalAlgebra.PointwiseNormalizedWeightHom
/-!
概要：指定単位余積の正規化Homを同じ自由正規化鎖随伴へ照合する。
方針：元の正規化Homの前合成則と指定生成元の像で各単体を計算する。
規約：IS-W2 B02の同じ係数移送の証明分割。余積・自由加群の指定射を保持する。
使われ方：HA 1.2.4、元の線形BK重みとA09の自由鎖比較の全単体照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 指定生成元を保つ係数同型による移送は同じ自由鎖Hom随伴と一致する。 -/
theorem copowerNormalizedHomEquiv_free (W : SSet.{0}) (H : Complex A)
    (f : ((normalizedMooreComplex (ModuleCat A)).obj
      (W ⋙ uliftFunctor.{u,0} ⋙ ModuleCat.free A)).extend
          ComplexShape.embeddingDownNat ⟶ H) :
    copowerUnitDiagramHomEquiv A W
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ _).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))
      (normalizedWeightHomEquiv (W ⋙ copowerFunctor (ModuleCat.of A A)) H
        (HomologicalComplex.extendMap
          ((normalizedMooreComplex (ModuleCat A)).map
            (Functor.isoWhiskerLeft W (copowerUnitFreeNatIso A)).hom)
          ComplexShape.embeddingDownNat ≫ f)) =
    (freeNegativeChainsAdjunction A).homEquiv (W ⋙ uliftFunctor.{u,0}) H f := by
  rw [normalizedWeightHomEquiv_precomp, normalizedWeightHomEquiv_asAdjunction]
  simp only [freeNegativeChainsAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply]
  let g : W ⋙ uliftFunctor.{u,0} ⋙ ModuleCat.free A ⟶
      (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ _).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :=
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv _ _
      ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv _ H f)
  change copowerUnitDiagramHomEquiv A W _
      ((Functor.isoWhiskerLeft W (copowerUnitFreeNatIso A)).hom ≫ g) =
    (Adjunction.whiskerRight SimplexCategoryᵒᵖ (ModuleCat.adj A)).homEquiv
      (W ⋙ uliftFunctor.{u,0}) _ g
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  change (g.app n) (copowerUnitFreeHom A (W.obj n)
      (Sigma.ι (fun _ : W.obj n => ModuleCat.of A A) s.down (1 : A))) =
    (g.app n) (ModuleCat.freeMk s)
  erw [copowerUnitFreeHom_generator]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

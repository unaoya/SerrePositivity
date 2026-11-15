module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom

/-!
# 指定正規化標準単体 Hom と同じ自由鎖随伴

概要：標準単体Hom同値を、同じ自由鎖随伴の恒等単体での評価に同定する。
方針：零延長随伴の逆写像を照合し、自由加群とDKの指定随伴を合成する。
規約：IS-W2 B02のパラメータ側の同じ係数移送の分割。
使われ方：HA 1.2.4、A09のtensor–Homと実Hom単体の指定比較の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：指定正規化単体Hom同値は同じ自由随伴の恒等生成元の値。
方針：二つの零延長Hom同値の逆写像を同定し、元のDK・自由随伴を使う。
規約：任意の複体と単体次数。使われ方：HA 1.2.4 の実AW比較のパラメータ照合。 -/
theorem normalizedSimplexHomEquiv_freeAdjunction (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    ((freeNegativeChainsAdjunction A).homEquiv
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f).app (Opposite.op n)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n))) =
    normalizedSimplexHomEquiv A H n f := by
  have hm (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
      (he : e = ComplexShape.embeddingUpIntLE 0) (L : ChainComplex (ModuleCat A) ℕ) :
      extendTruncationHomEquivOfShape A e he L H =
        extendTruncationHomEquivOfEmbedding e he L H := by
    subst e
    apply Equiv.symm_bijective.injective
    ext g
    rfl
  have hn : (negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv
      ((normalizedMooreComplex (ModuleCat A)).obj
        ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
          (SSet.stdSimplex.obj n))) H f =
      normalizedChainsTruncationHomEquiv A (SSet.stdSimplex.obj n) H f := by
    simp only [negativeExtendTruncationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      normalizedChainsTruncationHomEquiv]
    rw [hm]
    rfl
  simp only [freeNegativeChainsAdjunction, Adjunction.comp_homEquiv]
  change ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv
        ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
          (SSet.stdSimplex.obj n)) (H.truncLE' (ComplexShape.embeddingUpIntLE 0))
        ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv _ H f)).app
      (Opposite.op n) (ModuleCat.freeMk (ULift.up
        (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) = _
  have hd := congrArg (fun k =>
    ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.homEquiv
        ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
          (SSet.stdSimplex.obj n)) (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) k).app
      (Opposite.op n) (ModuleCat.freeMk (ULift.up
        (SSet.stdSimplex.objEquiv.symm (𝟙 n))))) hn
  exact hd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

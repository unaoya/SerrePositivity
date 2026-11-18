module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexContraction

/-!
# 標準単体の整数次数での実収縮

概要：元の正規化単体を次数零の A へ収縮する。
方針：鎖収縮と二つのホモトピーを q ↦ −q に沿って延長する。
規約：複体は非有界の既存 Complex A、終域はそのテンソル単位。
使われ方：任意の複体にテンソルする標準単体の実 augmentation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def normalizedSimplexCochainContraction (n : SimplexCategory) :
    HomotopyEquiv ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))
      (𝟙_ (Complex A)) := by
  let h := _root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n
  let e := ComplexShape.embeddingDownNat
  let h' : HomotopyEquiv
      (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).extend e)
      (((ChainComplex.single₀ (ModuleCat A)).obj (𝟙_ (ModuleCat A))).extend e) := {
    hom := HomologicalComplex.extendMap h.hom e
    inv := HomologicalComplex.extendMap h.inv e
    homotopyHomInvId := by
      simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id]
        using h.homotopyHomInvId.extend e
    homotopyInvHomId := by
      simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id]
        using h.homotopyInvHomId.extend e }
  exact h'.trans (HomotopyEquiv.ofIso
    (HomologicalComplex.extendSingleIso e (𝟙_ (ModuleCat A)) 0 0 rfl))

end SerrePositivity.ComplexLimits

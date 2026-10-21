module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompIdentityMorphism
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphComparison
/-!
概要：元の出力模型比較を、その指定射と可換四角形で照合する。
方針：同じ全関手射の前合成と tensor 評価、元の合成比較の自然性を使う。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
lemma dgKernelDerivedInfinity_comp_graph_hom_naturality
    {Q Q' : BimoduleCategory R C D} (b : Q ⟶ Q')
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hQ' : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q')) :
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
        (BimoduleCategory.underlying R C D Q) (functorGraph R C E F) hQ).hom ≫
      (dgKernelDerivedFunctorHomFunctor R D E).map
        (BimoduleTensor.composeMap R E C D
          (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) b) =
    functorHomPostcomp
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (dgKernelDerivedInfinity R C E (functorGraph R C E F))
      ((dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
      (BimoduleCategory.underlying R C D Q') (functorGraph R C E F) hQ').hom := by
  have hh := dgKernelDerivedInfinity_compIso_hom_naturality R D C E b
    (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) hQ hQ'
    (dgFunctorGraph_rightRelativeKFlat R C E F)
    (dgFunctorGraph_rightRelativeKFlat R C E F)
  rw [CategoryTheory.Functor.map_id] at hh
  have hid : functorHomPrecomp
      (dgKernelDerivedInfinity R C E
        (BimoduleCategory.underlying R E C (BimoduleCategory.of R E C (functorGraph R C E F))))
      (dgKernelDerivedInfinity R C E
        (BimoduleCategory.underlying R E C (BimoduleCategory.of R E C (functorGraph R C E F))))
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (𝟙 ((dgKernelDerivedFunctorHomFunctor R C E).obj
        (BimoduleCategory.of R E C (functorGraph R C E F)))) = 𝟙 _ :=
    functorHomPrecomp_identity _ _
  rw [hid, Category.comp_id] at hh
  exact hh
end SerrePositivity.InfinityCategories

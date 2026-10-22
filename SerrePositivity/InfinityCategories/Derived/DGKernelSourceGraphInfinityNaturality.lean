module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionRightNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphComparison
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoTwoStepSquare
/-!
概要：元の graph 入力変更と元の kernel の実導来作用の任意射自然性を回収する。
方針：指定 graph 比較・κ・元の双加群同型の自然性を保持する。
規約：原 kernel に平坦性を追加しない。使われ方：元の始域制限と cell 入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C D)
variable {Q0 Q1 : BimoduleCategory R E D} (g : Q0 ⟶ Q1)
local notation "q0" => BimoduleCategory.underlying R E D Q0
local notation "q1" => BimoduleCategory.underlying R E D Q1
local notation "H0" => dgKernelDerivedInfinity R D E q0
local notation "H1" => dgKernelDerivedInfinity R D E q1
local notation "P" => functorGraph R C D F
local notation "J" => dgModuleExtensionInfinity R C D F
local notation "G" => dgKernelDerivedInfinity R C D P
lemma dgKernelDerivedInfinity_sourceGraphIso_hom_naturality :
    (dgKernelDerivedInfinity_sourceGraphIso R C D E F q0).hom ≫
      (dgKernelDerivedFunctorHomFunctor R C E).map
        (BimoduleTensor.composeMap R E D C g (𝟙 (BimoduleCategory.of R D C P))) =
    functorHomPrecomp H0 H1 J ((dgKernelDerivedFunctorHomFunctor R D E).map g) ≫
      (dgKernelDerivedInfinity_sourceGraphIso R C D E F q1).hom := by
  let e : FunctorIso J G := (dgKernelDerivedInfinity_graphIso R C D F).symm
  let a : FunctorHom H0 H1 := (dgKernelDerivedFunctorHomFunctor R D E).map g
  have he : (e.postcomp H0).hom ≫ functorHomPrecomp H0 H1 G a =
      functorHomPrecomp H0 H1 J a ≫ (e.postcomp H1).hom := by
    simpa only [functorIso_postcomp_hom_typed] using!
      functorHom_whisker_exchange_typed e.hom a
  have hk := dgKernelDerivedInfinity_compIso_right_naturality R C D E
    (BimoduleCategory.of R D C P) g (dgFunctorGraph_rightRelativeKFlat R C D F)
  exact functorIso_trans_hom_square (e.postcomp H0) (e.postcomp H1)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R C D E P q0
      (dgFunctorGraph_rightRelativeKFlat R C D F))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R C D E P q1
      (dgFunctorGraph_rightRelativeKFlat R C D F))
    (functorHomPrecomp H0 H1 J a) (functorHomPrecomp H0 H1 G a)
    ((dgKernelDerivedFunctorHomFunctor R C E).map
      (BimoduleTensor.composeMap R E D C g (𝟙 (BimoduleCategory.of R D C P)))) he hk
end SerrePositivity.InfinityCategories

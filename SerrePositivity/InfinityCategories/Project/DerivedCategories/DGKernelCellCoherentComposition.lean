module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedPentagonCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellCompositionSandwichValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalenceHomInvCorrection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichMiddleChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGeneralComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichPentagon
/-!
概要：coherent な中間比較を使う cell 合成子と旧合成子からの補正・五角式。
方針：同じ模型比較と一般 sandwich 合成子、指定 K-flat の五角式を使う。
規約：旧合成子の値を変更しない。使われ方：一般 cell の単位 coherence。
-/
@[expose] public section

universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K] (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E)
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "KC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K
local notation "MP" => BimoduleCategory.underlying R EC DC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P)
local notation "MQ" => BimoduleCategory.underlying R KC EC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q)
def dgKernelDerivedInfinity_compositionCellCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P Q) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).coherentHomInvIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC MP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC MQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R E K Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC MP MQ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P))
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_correction :
    dgKernelDerivedInfinity_compositionCellCoherentIso R D E K P Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellIso R D E K P Q ≪≫
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC MP MQ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P)).postcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).homInvCorrectionIso
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC MQ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC MP) ≪≫
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC MP MQ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P)).postcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom).precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_middle_change
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).homInvIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).coherentHomInvIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC MP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC MQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R E K Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC MP MQ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P))
end
section
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G] [Small.{u} G]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (S : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F)
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R F
local notation "GC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R G
local notation "L0" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D)
local notation "L1" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E)
local notation "L2" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R F)
local notation "L3" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R G)
local notation "s0" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.inv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D)
local notation "ε0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.coherentHomInvIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D)
local notation "s1" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.inv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E)
local notation "ε1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.coherentHomInvIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E)
local notation "s2" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.inv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R F)
local notation "ε2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.QCatEquivalence.coherentHomInvIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R F)
local notation "mP" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P)
local notation "hP" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P
local notation "mQ" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R FC EC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E F Q)
local notation "hQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R E F Q
local notation "mS" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R GC FC
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R F G S)
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R F G S
local notation "QP" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R FC EC DC mQ mP
local notation "SQ" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R GC FC EC mS mQ
local notation "HL" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R GC FC DC mS QP
local notation "HR" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R GC EC DC SQ mP
local notation "hQP" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite_rightRelativeKFlat R D E F P Q
local notation "O0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P
local notation "M0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC mP
local notation "O1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q
local notation "M1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC FC mQ
local notation "O2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R F G S
local notation "M2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R FC GC mS
local notation "M02" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC FC QP
local notation "M13" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC GC SQ
local notation "ML" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC GC HL
local notation "MR" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC GC HR
local notation "O02" => s0 ≫ M02 ≫ L2
local notation "O13" => s1 ≫ M13 ≫ L3
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R E F Q
local notation "c" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R F G S
local notation "k0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC FC mP mQ hP
local notation "k1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R EC FC GC mQ mS hQ
local notation "kl" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC FC GC QP mS hQP
local notation "kr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC GC mP SQ hP
local notation "K0" => dgKernelDerivedInfinity_compositionCellCoherentIso R D E F P Q
local notation "K1" => dgKernelDerivedInfinity_compositionCellCoherentIso R E F G Q S
local notation "KL" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s0 L2 s2 L3 ε2
  O02 O2 M02 M2 ML (Iso.refl _) c kl
local notation "KR" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s0 L1 s1 L3 ε1
  O0 O13 M0 M13 MR a (Iso.refl _) kr
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R DC GC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R GC FC EC DC mS mQ mP)
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_pentagon :
    (K0).postcomp O2 ≪≫ KL =
      (K1).precomp O0 ≪≫ KR ≪≫ ((e).postcomp L3).precomp s0 := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_pentagon R DC EC FC GC mP mQ mS hP hQ hS
  have hL0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L0).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R G)) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).isQCatEquivalence.precompose
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R G)).isFullyFaithful
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_pentagon L0 L1 L2 L3 s0 s1 s2 ε0 ε1 ε2
    O0 O1 O2 M0 M1 M2 M02 M13 ML MR a b c k0 k1 kl kr e hp hL0
  simpa only [dgKernelDerivedInfinity_compositionCellCoherentIso] using! ht
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories

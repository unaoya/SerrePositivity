module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCompositionSandwichValue
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedPentagonCoherence
/-!
概要：任意の元 kernel 三入力に対する元の cell 合成比較の五角式を証明する。
方針：指定された比較値と平坦模型の既存五角式を、始域同値から反映する。
規約：原 kernel の平坦性・三角式は仮定しない。使われ方：一般 cell の coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F G : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F] [DGCategory R G] [Small.{u} G]
  (P : Bimodule R E D) (Q : Bimodule R F E) (S : Bimodule R G F)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FC" => DGCategoryCellResolution.Source R F
local notation "GC" => DGCategoryCellResolution.Source R G
local notation "L0" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R D)
local notation "L1" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R E)
local notation "L2" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R F)
local notation "L3" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R G)
local notation "s0" => QCatEquivalence.inv (dgCellModuleSourceEquivalence R D)
local notation "ε0" => QCatEquivalence.homInvIso (dgCellModuleSourceEquivalence R D)
local notation "s1" => QCatEquivalence.inv (dgCellModuleSourceEquivalence R E)
local notation "ε1" => QCatEquivalence.homInvIso (dgCellModuleSourceEquivalence R E)
local notation "s2" => QCatEquivalence.inv (dgCellModuleSourceEquivalence R F)
local notation "ε2" => QCatEquivalence.homInvIso (dgCellModuleSourceEquivalence R F)
local notation "mP" => BimoduleCategory.underlying R EC DC
  (dgKernelCellModel R D E P)
local notation "hP" => dgKernelCellModel_rightRelativeKFlat R D E P
local notation "mQ" => BimoduleCategory.underlying R FC EC
  (dgKernelCellModel R E F Q)
local notation "hQ" => dgKernelCellModel_rightRelativeKFlat R E F Q
local notation "mS" => BimoduleCategory.underlying R GC FC
  (dgKernelCellModel R F G S)
local notation "hS" => dgKernelCellModel_rightRelativeKFlat R F G S
local notation "QP" => BimoduleTensor.compose R FC EC DC mQ mP
local notation "SQ" => BimoduleTensor.compose R GC FC EC mS mQ
local notation "HL" => BimoduleTensor.compose R GC FC DC mS QP
local notation "HR" => BimoduleTensor.compose R GC EC DC SQ mP
local notation "hQP" => dgKernelCellComposite_rightRelativeKFlat R D E F P Q
local notation "O0" => dgKernelDerivedInfinity R D E P
local notation "M0" => dgKernelDerivedInfinity R DC EC mP
local notation "O1" => dgKernelDerivedInfinity R E F Q
local notation "M1" => dgKernelDerivedInfinity R EC FC mQ
local notation "O2" => dgKernelDerivedInfinity R F G S
local notation "M2" => dgKernelDerivedInfinity R FC GC mS
local notation "M02" => dgKernelDerivedInfinity R DC FC QP
local notation "M13" => dgKernelDerivedInfinity R EC GC SQ
local notation "ML" => dgKernelDerivedInfinity R DC GC HL
local notation "MR" => dgKernelDerivedInfinity R DC GC HR
local notation "O02" => s0 ≫ M02 ≫ L2
local notation "O13" => s1 ≫ M13 ≫ L3
local notation "a" => dgKernelDerivedInfinity_cellModelIso R D E P
local notation "b" => dgKernelDerivedInfinity_cellModelIso R E F Q
local notation "c" => dgKernelDerivedInfinity_cellModelIso R F G S
local notation "k0" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC FC mP mQ hP
local notation "k1" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R EC FC GC mQ mS hQ
local notation "kl" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC FC GC QP mS hQP
local notation "kr" => dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC GC mP SQ hP
local notation "K0" => dgKernelDerivedInfinity_compositionCellIso R D E F P Q
local notation "K1" => dgKernelDerivedInfinity_compositionCellIso R E F G Q S
local notation "KL" => functorIsoSandwichCompositor s0 L2 s2 L3 ε2
  O02 O2 M02 M2 ML (Iso.refl _) c kl
local notation "KR" => functorIsoSandwichCompositor s0 L1 s1 L3 ε1
  O0 O13 M0 M13 MR a (Iso.refl _) kr
local notation "e" => dgKernelDerivedInfinity_bimoduleIso R DC GC
  (BimoduleTensor.associatorIso R GC FC EC DC mS mQ mP)
lemma dgKernelDerivedInfinity_compositionCellIso_pentagon :
    (K0).postcomp O2 ≪≫ KL =
      (K1).precomp O0 ≪≫ KR ≪≫ ((e).postcomp L3).precomp s0 := by
  have hp := dgKernelDerivedInfinity_compIso_pentagon R DC EC FC GC mP mQ mS hP hQ hS
  have hL0 : IsFullyFaithful ((pre L0).app (dgModuleDerivedInfinityCategory R G)) :=
    ((dgCellModuleSourceEquivalence R D).isQCatEquivalence.precompose
      (dgModuleDerivedInfinityCategory R G)).isFullyFaithful
  have ht := functorIsoSandwichCompositor_pentagon L0 L1 L2 L3 s0 s1 s2 ε0 ε1 ε2
    O0 O1 O2 M0 M1 M2 M02 M13 ML MR a b c k0 k1 kl kr e hp hL0
  simpa only [dgKernelDerivedInfinity_compositionCellIso_sandwich] using! ht
end
end SerrePositivity.InfinityCategories

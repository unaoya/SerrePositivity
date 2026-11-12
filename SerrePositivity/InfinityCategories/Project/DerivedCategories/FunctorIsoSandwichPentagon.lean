module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichSourceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonLeftPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonRightPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionPentagonTransfer
/-!
概要：一般合成子の五角式を、同じモデル側五角式と始域比較から導く。
方針：元の比較正方形・水平結合律・完全充満な前合成による反映を使う。
規約：中間同値の三角式を仮定しない。使われ方：一般 cell 合成の五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X0 X1 X2 X3 A0 A1 A2 A3 : SSet.{u}}
  [Quasicategory X0] [Quasicategory X1] [Quasicategory X2]
  [Quasicategory A1] [Quasicategory A2] [Quasicategory A3]
  (L0 : X0 ⟶ A0) (L1 : X1 ⟶ A1) (L2 : X2 ⟶ A2) (L3 : X3 ⟶ A3)
  (s0 : A0 ⟶ X0) (s1 : A1 ⟶ X1) (s2 : A2 ⟶ X2)
  (ε0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L0 ≫ s0) (𝟙 X0))
  (ε1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L1 ≫ s1) (𝟙 X1))
  (ε2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L2 ≫ s2) (𝟙 X2))
  (F0 : A0 ⟶ A1) (F1 : A1 ⟶ A2) (F2 : A2 ⟶ A3)
  (G0 : X0 ⟶ X1) (G1 : X1 ⟶ X2) (G2 : X2 ⟶ X3)
  (G02 : X0 ⟶ X2) (G13 : X1 ⟶ X3) (TL TR : X0 ⟶ X3)
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F0 (s0 ≫ G0 ≫ L1))
  (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F1 (s1 ≫ G1 ≫ L2))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F2 (s2 ≫ G2 ≫ L3))
  (k0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G0 ≫ G1) G02) (k1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G1 ≫ G2) G13)
  (kl : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G02 ≫ G2) TL) (kr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G0 ≫ G13) TR)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso TR TL)
  (hp : k0.postcomp G2 ≪≫ kl = k1.precomp G0 ≪≫ kr ≪≫ e)
local notation "F02" => s0 ≫ G02 ≫ L2
local notation "F13" => s1 ≫ G13 ≫ L3
local notation "FL" => s0 ≫ TL ≫ L3
local notation "FR" => s0 ≫ TR ≫ L3
local notation "x0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison L0 s0 ε0 F0 (G0 ≫ L1) a
local notation "x1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison L1 s1 ε1 F1 (G1 ≫ L2) b
local notation "x2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison L2 s2 ε2 F2 (G2 ≫ L3) c
local notation "x02" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ε0 (G02 ≫ L2)
local notation "x13" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ε1 (G13 ≫ L3)
local notation "xl" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ε0 (TL ≫ L3)
local notation "xr" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ε0 (TR ≫ L3)
local notation "K0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s0 L1 s1 L2 ε1
  F0 F1 G0 G1 G02 a b k0
local notation "K1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s1 L2 s2 L3 ε2
  F1 F2 G1 G2 G13 b c k1
local notation "KL" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s0 L2 s2 L3 ε2
  F02 F2 G02 G2 TL (Iso.refl _) c kl
local notation "KR" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s0 L1 s1 L3 ε1
  F0 F13 G0 G13 TR a (Iso.refl _) kr
local notation "EL" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e L3) s0
include ε0 hp in
lemma functorIsoSandwichCompositor_pentagon_precomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((K0).postcomp F2 ≪≫ KL) L0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((K1).precomp F0 ≪≫ KR ≪≫ EL) L0 := by
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_source_comparison L0 s0 ε0 L1 s1 L2 ε1
    F0 F1 G0 G1 G02 a b k0
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_source_comparison L1 s1 ε1 L2 s2 L3 ε2
    F1 F2 G1 G2 G13 b c k1
  have hl0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_source_comparison L0 s0 ε0 L2 s2 L3 ε2
    F02 F2 G02 G2 TL (Iso.refl _) c kl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison_refl] at hl0
  have hr0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_source_comparison L0 s0 ε0 L1 s1 L3 ε1
    F0 F13 G0 G13 TR a (Iso.refl _) kr
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison_refl] at hr0
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonComposition_left_path L0 L1 L2 L3 F0 F1 F2 G0 G1 G2
    F02 FL G02 TL x0 x1 x2 x02 xl (K0) (KL) k0 kl h0 hl0
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonComposition_right_path L0 L1 L2 L3 F0 F1 F2 G0 G1 G2
    F13 FR G13 TR x0 x1 x2 x13 xr (K1) (KR) k1 kr h1 hr0
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso_assoc L0 L1 L2 L3 F0 F1 F2 G0 G1 G2 x0 x1 x2
  have ht : xr ≪≫ e.postcomp L3 = (EL).precomp L0 ≪≫ xl := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange ε0 (e.postcomp L3)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp] using! h
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pentagonComparison_transfer L0 L3 ((F0 ≫ F1) ≫ F2) FL FR
    ((G0 ≫ G1) ≫ G2) TL TR xl xr _ _ ((K0).postcomp F2 ≪≫ KL)
    ((K1).precomp F0 ≪≫ KR) (k0.postcomp G2 ≪≫ kl)
    (k1.precomp G0 ≪≫ kr) (EL) e hl hr hn ht
    (by simpa only [Iso.trans_assoc] using! hp)
  simpa only [Iso.trans_assoc] using! h
include ε0 hp in
lemma functorIsoSandwichCompositor_pentagon
    (hL0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L0).app A3)) :
    (K0).postcomp F2 ≪≫ KL = (K1).precomp F0 ≪≫ KR ≪≫ EL := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_eq_of_isFullyFaithful L0 hL0 _ _
    (functorIsoSandwichCompositor_pentagon_precomp L0 L1 L2 L3 s0 s1 s2 ε0 ε1 ε2
      F0 F1 F2 G0 G1 G2 G02 G13 TL TR a b c k0 k1 kl kr e hp)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories

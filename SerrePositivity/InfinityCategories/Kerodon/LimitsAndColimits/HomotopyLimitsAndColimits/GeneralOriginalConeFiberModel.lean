module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralConeFiberReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralConeFiberModel
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralOriginalCriterion

/-!
概要：任意の小圏上の pinched Hom を元の非反転 q_x の導来 fiber 全体の ULift と直接比較する。
方針：反転 end の fiber 模型を edgewise 共通解像で元の fiber へ移し、ULift 後に合成する。
規約：局所 Kan 性だけを要求し、反転した fiber や追加の比較同値の入力を残さない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、A3d による γ3b の一般の検出。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

local instance generalOriginalModel_homKan (F : I ⥤ C) (x : C) :
    ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)))

local instance generalOriginalModel_opKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance generalOriginalModel_holimKan (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H

local instance generalOriginalModel_pointKan {F : I ⥤ C} (c : Cone F) (x : C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom x c.pt))

local instance generalOriginalModel_opPointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

/-- 概要：coherent な錐の標準点から回収した元の非反転 end の点。
方針：標準切断点に対応する反転 end の点を edgewise end の左右の射影で移す。
規約：元の錐 d と局所 Kan 性だけから点を定め、逆の選択を固定する。
使われ方：一般形状の元の q_x の導来 fiber の固定点。 -/
def generalStrictConeOriginalEndPoint {F : I ⥤ C} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanGeneralReflectedFiberPoint _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.generalStrictConeReflectedEndPoint d)

/-- 概要：任意の錐から strict な錐への pinched Hom は元の q_x の導来 fiber の ULift と同値。
方針：一般の反転 fiber 模型と、edgewise 共通解像の fiber の同値の ULift を合成する。
規約：fiber 全体の反転はなく、Hom の厳密極限性や追加の比較の同値性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、元の非反転比較を使う A3d の直接模型。 -/
def strictConePinched_generalOriginalEnd_equivalence {F : I ⥤ C}
    (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (generalStrictConeOriginalEndPoint d))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeFiber_generalReflection_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.generalStrictConeReflectedEndPoint d)
  have he := e.isQCatEquivalence.isSimplicialHomotopyEquivalence
  let e' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence.{u, v} he).isQCatEquivalence.choose
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConePinched_generalReflectedEnd_equivalence c d).trans e'

/-- 概要：一般の錐の pinched Hom の可縮性は元の q_x の固定点の fiber 模型の可縮性と同値。
方針：構成した直接の同値で可縮 Kan 性を保存し反映する。
規約：可縮性は全境界の充填であり、単なる π₀ の一意性に弱めない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、A3d の検出を元の q_x へ移す。 -/
lemma strictConePinched_isContractibleKan_iff_generalOriginalEnd {F : I ⥤ C}
    (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
        (generalStrictConeOriginalEndPoint d))) :=
  (strictConePinched_generalOriginalEnd_equivalence c d).isContractibleKan_iff

/-- 概要：一般の native な極限性は全ての錐の標準点での元の q_x の fiber 模型で検出できる。
方針：A3d の全 pinched Hom の可縮性を直接の fiber 模型の可縮性へ置き換える。
規約：全 coherent な錐 d を量化し、strict な錐だけには制限しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、γ3b の一般の具体的な判定。 -/
lemma strictCoherentCone_isLimit_iff_generalOriginalEndPointFibers {F : I ⥤ C}
    (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (generalStrictConeOriginalEndPoint d))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_iff_conePinchedHom_isContractibleKan]
  exact forall_congr' fun d ↦ strictConePinched_isContractibleKan_iff_generalOriginalEnd c d

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

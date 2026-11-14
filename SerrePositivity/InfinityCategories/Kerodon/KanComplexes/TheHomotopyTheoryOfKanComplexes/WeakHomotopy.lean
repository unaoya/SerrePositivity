module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 標的へのホモトピー類による弱ホモトピー同値と弱可縮性。
方針：全ての Kan 複体 Z について π₀ Fun(-,Z) による検査を行う。
規約：検査する射の始域・終域に Kan 性や quasicategory 性を課さない。
使われ方：Kerodon §3.1.7（Tag 00U1）、§7.2.3（Tag 02NX） の Quillen A の弱可縮性条件。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：π₀ の合成則を関数の等式として表示する。
方針：Mathlib の各点の計算則に関数外延性を適用する。
規約：合成順序は単体集合の射の順序。
使われ方：弱ホモトピー同値の二対三則。 -/
lemma mapPiZero_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    SSet.mapπ₀ (f ≫ g) = SSet.mapπ₀ g ∘ SSet.mapπ₀ f :=
  funext (SSet.mapπ₀_comp_apply f g)

/-- 概要：π₀ の恒等則を関数の等式として表示する。
方針：Mathlib の各点の計算則に関数外延性を適用する。
規約：A は任意の単体集合。
使われ方：弱ホモトピー同値の恒等射。 -/
lemma mapPiZero_id (A : SSet.{u}) : SSet.mapπ₀ (𝟙 A) = id :=
  funext SSet.mapπ₀_id_apply

/-- 概要：全ての Kan 標的へのホモトピー類で検査する弱ホモトピー同値。
方針：前合成が写像空間の連結成分の全単射を与えると要求する。
規約：元の単体集合の Kan 性は要求しない。検査標的の宇宙は同じ u。
使われ方：Kerodon §3.1.7（Tag 00U1） の定義、Quillen A。 -/
@[kerodon 00UA]
def IsWeakHomotopyEquivalence {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∀ (Z : SSet.{u}) [KanComplex Z], Function.Bijective (SSet.mapπ₀ ((pre f).app Z))

/-- 概要：一点への射が弱ホモトピー同値であるという弱可縮性。
方針：選ばれた終対象への射に Kan 標的による検査を適用する。
規約：K 自体の Kan 性や全境界の充填を定義に含めない。
使われ方：Kerodon §7.2.3（Tag 02NX） の slice の条件。 -/
@[kerodon 04GW]
def IsWeaklyContractible (K : SSet.{u}) : Prop :=
  IsWeakHomotopyEquivalence (terminal.from K)

/-- 概要：恒等射は弱ホモトピー同値。
方針：内部 Hom の前合成の恒等則を用いる。
規約：A は任意の単体集合。
使われ方：Kerodon §3.1.7（Tag 00U1） の基本例。 -/
lemma isWeakHomotopyEquivalence_id (A : SSet.{u}) :
    IsWeakHomotopyEquivalence (𝟙 A) := by
  intro Z hZ
  rw [pre_id, NatTrans.id_app]
  simpa only [mapPiZero_id] using Function.bijective_id (α := SSet.π₀ ((ihom A).obj Z))

/-- 概要：弱ホモトピー同値は合成で閉じる。
方針：前合成の順序の反転と π₀ の関手性を使う。
規約：三つの単体集合は任意。
使われ方：Kerodon §3.1.7（Tag 00U1）、Quillen A の因子分解。 -/
lemma IsWeakHomotopyEquivalence.comp {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (f ≫ g) := by
  intro Z hZ
  simpa only [pre_map, NatTrans.comp_app, mapPiZero_comp, Function.comp_def]
    using (hf Z).comp (hg Z)

/-- 概要：f と f≫g が弱ホモトピー同値なら g もそうである。
方針：Kan 標的への π₀ の全単射を消去する。
規約：始域の充填性は不要。
使われ方：Kerodon §3.1.7（Tag 00U1）、弱可縮性の移送。 -/
lemma IsWeakHomotopyEquivalence.cancel_left {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsWeakHomotopyEquivalence f) (hfg : IsWeakHomotopyEquivalence (f ≫ g)) :
    IsWeakHomotopyEquivalence g := by
  intro Z hZ
  apply ((hf Z).of_comp_iff' (SSet.mapπ₀ ((pre g).app Z))).mp
  simpa only [pre_map, NatTrans.comp_app, mapPiZero_comp, Function.comp_def] using hfg Z

/-- 概要：g と f≫g が弱ホモトピー同値なら f もそうである。
方針：Kan 標的への π₀ の全単射を逆の因子で消去する。
規約：終域の充填性は不要。
使われ方：Kerodon §3.1.7（Tag 00U1）、弱可縮性の移送。 -/
lemma IsWeakHomotopyEquivalence.cancel_right {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hg : IsWeakHomotopyEquivalence g) (hfg : IsWeakHomotopyEquivalence (f ≫ g)) :
    IsWeakHomotopyEquivalence f := by
  intro Z hZ
  apply (Function.Bijective.of_comp_iff (SSet.mapπ₀ ((pre f).app Z)) (hg Z)).mp
  simpa only [pre_map, NatTrans.comp_app, mapPiZero_comp, Function.comp_def] using hfg Z

/-- 概要：全ての quasicategory への前合成が同値なら弱ホモトピー同値。
方針：Kan 標的に特殊化し、写像空間の実際のホモトピー逆から π₀ の全単射を得る。
規約：元の二つの単体集合は quasicategory でなくてもよい。
使われ方：Kerodon Remark 4.5.4.4（Tag 01EB）、Quillen A の比較模型。 -/
lemma IsPrecompositionEquivalence.isWeakHomotopyEquivalence {A B : SSet.{u}}
    {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : IsWeakHomotopyEquivalence f :=
  fun Z _ ↦ (hf Z).isSimplicialHomotopyEquivalence.mapPiZero_bijective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence (isWeakHomotopyEquivalence)


/-- 概要：quasicategory の同値は弱ホモトピー同値。
方針：全ての quasicategory への前合成による同値に移す。
規約：この補題では元の両対象が quasicategory。
使われ方：Kerodon Remark 4.5.4.4（Tag 01EB）、slice 模型の交換。 -/
@[kerodon 04FA]
lemma IsQCatEquivalence.isWeakHomotopyEquivalence {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    IsWeakHomotopyEquivalence f := hf.isPrecompositionEquivalence.isWeakHomotopyEquivalence

/-- 概要：弱ホモトピー同値に沿って弱可縮性を移す。
方針：終対象への射の合成則と弱ホモトピー同値の二対三則を使う。
規約：両対象の Kan 性は不要。
使われ方：Kerodon §7.2.3（Tag 02NX） の弱可縮な slice の比較。 -/
lemma IsWeakHomotopyEquivalence.weaklyContractible_iff {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsWeakHomotopyEquivalence f) : IsWeaklyContractible A ↔ IsWeaklyContractible B := by
  change IsWeakHomotopyEquivalence (terminal.from A) ↔
    IsWeakHomotopyEquivalence (terminal.from B)
  have he : f ≫ terminal.from B = terminal.from A := terminal.hom_ext _ _
  constructor
  · intro h
    exact hf.cancel_left (he.symm ▸ h)
  · intro h
    exact he ▸ hf.comp h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.3.5" (partial := component) "仮定：可縮な二つの Kan 複体と任意の射（原典の第一の明記された観察と一致）。結論：一点への二射が弱同値なので cancel_right と Kan Whitehead により、その射は単体ホモトピー同値。一文目に一致するが、これを用いた left fibration の輸送 criterion と hT→H の関手性の議論は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.cancel_right
attribute [cite HTT "2.2.2.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence

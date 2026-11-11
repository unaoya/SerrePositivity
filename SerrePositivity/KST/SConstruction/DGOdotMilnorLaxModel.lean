module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNativePerfect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableLaxStructure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedExactness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：元小 Perf 二因子と同じ Hom 双加群の D2 lax 模型を K-10 へ公開する。
方針：元 native gluing の同じ比較同値を、同宇宙の厳密な ULift 同型で戻す。
規約：二射影と比較の全単体を保つ。元代数射の固定 ν 模型との照合は別工程。
使われ方：resolved Verdier 列を実 lax 模型へ輸送する比較口。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)
local notation "D" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)
local notation "V" => DGSmallPerfectSquareCorner R (A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "p" => dgSmallPerfectSquareLeftMap R (A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "q" => dgSmallPerfectSquareRightMap R (A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "M" => dgHomGluingBimodule R (C) (D) (V) (p) (q)
local notation "hC" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorLeft_isDGPretriangulated R d
local notation "hD" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorRight_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d

/-- 概要：元の左小 Perf 因子の同じ native 安定値。
方針：D2 の宇宙共通化を使う。規約：対象を変更しない。使われ方：lax 第一因子。 -/
abbrev dgOdotMilnorLaxLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, u + 1, u + 1} R (C) (hC)

/-- 概要：元の右小 Perf 因子の同じ native 安定値。
方針：D2 の宇宙共通化を使う。規約：対象を変更しない。使われ方：lax 第二因子。 -/
abbrev dgOdotMilnorLaxRight : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, u + 1, u + 1} R (D) (hD)

/-- 概要：同じ実 Yoneda と Hom 係数を評価する導来加群圏。
方針：D2 正本の基底を使う。規約：元代数の角の ν 値との同一視はしない。
使われ方：元二因子を保つ実 lax 模型。 -/
abbrev dgOdotMilnorLaxBase : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableModuleCategory.{u, u + 1, u + 1} R (C)

/-- 概要：元の小 Perf 第一因子の実導来 Yoneda。
方針：D2 の完全性供給を使う。規約：二脚の完全性を追加仮定しない。
使われ方：実 lax 模型の第一脚。 -/
def dgOdotMilnorLaxYoneda : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorLaxLeft R d) (dgOdotMilnorLaxBase R d) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (C),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor R (C) (hC)⟩

/-- 概要：元の Hom 双加群を使う第二因子の実導来係数。
方針：D2 の完全性供給を使う。規約：元の下辺・右辺由来の双加群を保つ。
使われ方：実 lax 模型の第二脚。 -/
def dgOdotMilnorLaxCoefficient : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorLaxRight R d)
    (dgOdotMilnorLaxBase R d) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (C) (D) (M),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R (C) (D) (M) (hD)⟩

/-- 概要：元の二因子・Hom 係数を持つ具体的 lax 安定圏。
方針：Sp 正本を同じ二脚に適用する。規約：抽象的な同値先を選ばない。
使われ方：native Verdier 列を移す実中央対象。 -/
abbrev dgOdotMilnorLaxCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} :=
  laxCategory (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)

/-- 概要：元 native gluing の同宇宙 ULift の厳密な表示同型。
方針：型の ULift 自然同型を各次数へ適用する。規約：全単体を保持する。
使われ方：D2 の比較を同じ native 始域で使う。 -/
def dgOdotMilnorNativeLiftIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) ≅
    (SSet.uliftFunctor.{u + 1, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) :=
  (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) CategoryTheory.uliftFunctorTrivial ≪≫
    Functor.rightUnitor _).symm

/-- 概要：元 native gluing と D2 の同じ実 lax 模型の同値。
方針：厳密 ULift 表示同型と正本比較を合成する。
規約：元二射影を後続の等式で回収する。使われ方：resolved 射影の輸送。 -/
def dgOdotMilnorNativeLaxEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d).obj (dgOdotMilnorLaxCategory R d).obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (dgOdotMilnorNativeLiftIso R d)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R (C) (D) (M))

/-- 概要：同じ native 比較を完全射へ束ねる。
方針：同値の完全性を使う。規約：比較の全単体は不変。
使われ方：元包含との合成と商の逆輸送。 -/
def dgOdotMilnorNativeLaxComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d)
    (dgOdotMilnorLaxCategory R d) :=
  ⟨(dgOdotMilnorNativeLaxEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (dgOdotMilnorNativeLaxEquivalence R d).isQCatEquivalence⟩

/-- 概要：第一射影は元 gluing の第一射影を全単体で回収する。
方針：D2 正本の厳密射影式。規約：ホモトピー圏だけの一致ではない。
使われ方：元の左小 Perf 因子への照合。 -/
lemma dgOdotMilnorNativeLaxComparison_fst :
    (dgOdotMilnorNativeLaxComparison R d).hom ≫
      (laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom =
        (dgOdotMilnorNativeLiftIso R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R (C) (D) (M) := by
  change ((dgOdotMilnorNativeLiftIso R d).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R (C) (D) (M)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (C) (D) (M)) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst]

/-- 概要：第二射影も元 gluing の第二射影を全単体で回収する。
方針：D2 正本の厳密射影式。規約：因子の順序を保つ。
使われ方：元の右小 Perf 因子への照合。 -/
lemma dgOdotMilnorNativeLaxComparison_snd :
    (dgOdotMilnorNativeLaxComparison R d).hom ≫
      (laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom =
        (dgOdotMilnorNativeLiftIso R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R (C) (D) (M) := by
  change ((dgOdotMilnorNativeLiftIso R d).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R (C) (D) (M)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, u + 1, u + 1} R (C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R (C) (D) (M)) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd]

/-- 概要：第一因子は coherent 冪等完備。
方針：同じ元小 Perf の完備性を ULift へ移す。規約：追加仮定なし。
使われ方：Cat^perf の Tamme 分裂。 -/
lemma dgOdotMilnorLaxLeft_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgOdotMilnorLaxLeft R d).obj :=
  (dgOdotMilnorNativeLeft_complete R d).ulift

/-- 概要：第二因子も coherent 冪等完備。
方針：同じ元小 Perf の完備性を ULift へ移す。規約：追加仮定なし。
使われ方：Cat^perf の Tamme 分裂。 -/
lemma dgOdotMilnorLaxRight_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgOdotMilnorLaxRight R d).obj :=
  (dgOdotMilnorNativeRight_complete R d).ulift

end SerrePositivity.KST.SConstruction

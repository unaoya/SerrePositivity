module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedChain
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 標準成分模型と Mathlib Dold–Kan 対象の同型

概要：標準成分模型と N4 の線形 Hom を実際の Mathlib Γ に自然同型で同定する。
方針：計算した正規化の複体同型を Dold–Kan 同値の unit で単体的加群へ戻す。
規約：各次数の同値だけでなく全ての面・退化と可換な同型を得る。
使われ方：HA 1.3.1.13–1.3.1.14、Kerodon 2.5.9.2（Tag 00SE） の DK Hom と局所 Kan 性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準成分の単体的加群は切断 Hom に Mathlib Γ を適用したものと自然同型である。
方針：Dold–Kan 同値の unit と正規化の複体同型への Γ の作用を合成する。
規約：全ての単調写像について自然な単体的加群の同型。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.2（Tag 00SE） の標準 Hom の DK への厳密な同定。 -/
@[kerodon 00SE]
def standardDoldKanModuleIso (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomModule (R := R) x y :=
  (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat.{u} R) ≌
    ChainComplex (ModuleCat.{u} R) ℕ).unitIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) ≪≫
      (Abelian.DoldKan.Γ : ChainComplex (ModuleCat.{u} R) ℕ ⥤
        SimplicialObject (ModuleCat.{u} R)).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y)

/-- 概要：N4 の線形 Hom の単体的加群は実際の Mathlib Γ の Hom と自然同型である。
方針：次数符号による標準座標への変換と標準模型の DK 同型を合成する。
規約：N4 の微分の符号の補正もこの自然同型に含む。
使われ方：HA 1.3.1.13 の豊穣化の Hom と pinched Hom の接続。 -/
def homModuleDoldKanIso (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomModule (R := R) x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x y ≪≫ standardDoldKanModuleIso (R := R) x y

/-- 概要：小さい N4 の Hom 空間と実際の DK Hom 空間は単体集合として同型である。
方針：単体的加群の同型を加群の忘却関手へ送る。
規約：単体集合の射と逆射が全ての面・退化と可換である。
使われ方：HA 1.3.1.13–1.3.1.14 の局所 Kan 性と dg nerve の写像空間との比較。 -/
def homSpaceDoldKanIso (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpace (R := R) x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x y :=
  Functor.isoWhiskerRight (homModuleDoldKanIso (R := R) x y) (forget (ModuleCat.{u} R))

/-- 概要：宇宙を持ち上げた実際の DK Hom は dg nerve の右 pinched Hom と同型である。
方針：小さい N4 の Hom との同型を宇宙の持ち上げと合成する。
規約：coherent nerve の pinched Hom の比較とは区別し、dg nerve の Hom を同定する。
使われ方：HA 1.3.1.13 の単体的 Hom と dg nerve の写像空間の接続。 -/
def doldKanHomPinchedIso (x y : D) :
    SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y :=
  SSet.uliftFunctor.{v, u}.mapIso (homSpaceDoldKanIso (R := R) x y).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := R) x y

open SSet.modelCategoryQuillen in
/-- 概要：実際の Mathlib Γ による Hom 空間は Kan 複体である。
方針：N4 の直接の線形充填による Kan 性を単体集合の同型の逆射に沿って移す。
規約：単体的アーベル群の一般的な Kan 定理を追加仮定としていない。
使われ方：HA 1.3.1.14、Kerodon 2.5.9.2（Tag 00SE） の局所 Kan 性。 -/
instance doldKanHomSpaceKan (x y : D) : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x y) :=
  HomotopicalAlgebra.isFibrant_of_fibration (homSpaceDoldKanIso (R := R) x y).inv

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

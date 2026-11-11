module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionPushforward
public import Mathlib.CategoryTheory.Limits.Presheaf
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：標準単体上の旗の解像を全ての単体集合へ拡張する。
方針：Yoneda 埋め込みに沿う左 Kan 拡張と制限 Yoneda 関手の随伴を使う。
規約：通常の単体集合の圏で構成する。coherent Hom との同定は別途行う。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、補助解像とその射影の一般化。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体集合の旗の解像を Yoneda に沿う左 Kan 拡張で定める。
方針：標準単体上の余単体的な旗の図式を拡張する。
規約：𝒮 ではなく通常の単体集合の圏の関手。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、補助解像 Φ の組み立て。 -/
noncomputable def coherentResolution : SSet.{u} ⥤ SSet.{u} :=
  SSet.stdSimplex.{u}.leftKanExtension _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}

/-- 概要：旗の解像からの写像を単体として持つ右随伴の候補。
方針：標準単体の旗の図式に対する制限 Yoneda 関手を使う。
規約：coherent nerve の Hom との同定はここでは主張しない。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗を使う写像の普遍性の準備。 -/
noncomputable def coherentResolutionRightAdjoint : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}

/-- 概要：旗の解像の関手と制限 Yoneda 関手の随伴。
方針：Yoneda に沿う左 Kan 拡張の標準随伴を適用する。
規約：通常の圏としての随伴。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗の解像を通じた写像の対応。 -/
noncomputable def coherentResolutionAdjunction :
    coherentResolution.{u} ⊣ coherentResolutionRightAdjoint :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u})
    (SSet.stdSimplex.{u}.leftKanExtensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u})

/-- 概要：標準単体で評価した一般の解像は元の旗の解像と同型。
方針：Yoneda に沿う左 Kan 拡張が元の図式を延長することを使う。
規約：余単体的な図式の自然同型。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、一般構成の標準単体での回収。 -/
noncomputable def coherentResolutionStdIso :
    SSet.stdSimplex.{u} ⋙ coherentResolution ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram :=
  Presheaf.isExtensionAlongULiftYoneda _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}

/-- 概要：一般の解像は標準単体上の図式の左 Kan 拡張。
方針：選択した左 Kan 拡張の標準インスタンスを明示する。
規約：単位は Yoneda に沿う標準の単位を使う。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、一般の射影の普遍性による構成。 -/
instance coherentResolution_isLeftKanExtension :
    coherentResolution.{u}.IsLeftKanExtension
      (SSet.stdSimplex.{u}.leftKanExtensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}) :=
  inferInstanceAs (Functor.IsLeftKanExtension
    (SSet.stdSimplex.{u}.leftKanExtension _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u})
    (SSet.stdSimplex.{u}.leftKanExtensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}))

/-- 概要：解像から元の単体集合への自然な射影。
方針：標準単体上の最大元の射影を左 Kan 拡張の普遍性で延長する。
規約：一般の単体集合に対する同値性はここでは主張しない。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、射影 ρ の一般構成。 -/
noncomputable def coherentResolutionProjectionAll : coherentResolution.{u} ⟶ 𝟭 SSet :=
  coherentResolution.descOfIsLeftKanExtension
    (SSet.stdSimplex.{u}.leftKanExtensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u})
    (𝟭 SSet) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat

/-- 概要：一般の解像の射影は標準単体で元の最大元の射影を回収する。
方針：左 Kan 拡張からの降下の可換式を評価する。
規約：標準単体での自然同型の逆射を前に合成して比較する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、一般の射影と単体ごとの射影の整合性。 -/
lemma coherentResolutionProjectionAll_std (n : ℕ) :
    coherentResolutionStdIso.{u}.inv.app ⦋n⦌ ≫
      coherentResolutionProjectionAll.app Δ[n] = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := by
  exact coherentResolution.descOfIsLeftKanExtension_fac_app
    (SSet.stdSimplex.{u}.leftKanExtensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u})
    (𝟭 SSet) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat ⦋n⦌

/-- 概要：旗の解像を始域に持つ射と右随伴を標的に持つ射の対応。
方針：構成した随伴の Hom の同値を使う。
規約：任意の二つの単体集合に適用する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の普遍性の抽象的な部分。 -/
noncomputable def coherentResolutionHomEquiv (X Y : SSet.{u}) :
    (coherentResolution.obj X ⟶ Y) ≃ (X ⟶ coherentResolutionRightAdjoint.obj Y) :=
  coherentResolutionAdjunction.homEquiv X Y

/-- 概要：一般の解像の射影は標準単体で前合成による同値を与える。
方針：標準単体での回収同型を通じて、旗の最大元の射影の同値性を移す。
規約：標準単体に対する主張であり、一般の単体集合への主張は含まない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、一般の射影の基本となる単体の場合。 -/
lemma coherentResolutionProjectionAll_std_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionProjectionAll.{u}.app Δ[n]) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (coherentResolutionStdIso.{u}.app ⦋n⦌).symm).cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionStdIso.inv.app ⦋n⦌ ≫
    coherentResolutionProjectionAll.app Δ[n])
  rw [coherentResolutionProjectionAll_std]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection_isPrecompositionEquivalence n

/-- 概要：解像の随伴の Hom 対応を各単体で計算する。
方針：Yoneda に沿う左 Kan 拡張の随伴の標準計算則を使う。
規約：単体 x の表示を解像で写し、その後に f を合成する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、具体的な写像との比較の計算則。 -/
lemma coherentResolutionHomEquiv_app {X Y : SSet.{u}}
    (f : coherentResolution.obj X ⟶ Y) {d : SimplexCategoryᵒᵖ} (x : X.obj d) :
    (coherentResolutionHomEquiv X Y f).app d x =
      ULift.up (coherentResolutionStdIso.inv.app d.unop ≫
        coherentResolution.map (SSet.yonedaEquiv.symm x) ≫ f) := by
  exact Presheaf.uliftYonedaAdjunction_homEquiv_app
    (L := coherentResolution.{u}) (α := SSet.stdSimplex.{u}.leftKanExtensionUnit
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.{u}) f x

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

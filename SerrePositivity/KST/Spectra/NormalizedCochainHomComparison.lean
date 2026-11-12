module

public import SerrePositivity.KST.Spectra.ContravariantChainHom
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedCochainComplex

/-!
概要：正規化 cochain と通常の鎖からの Hom のホモトピー同値。
方針：Mathlib の正規化の鎖ホモトピー同値を反変 Hom へ送り、生成子の表示へ移す。
規約：係数の入射性や有理性は要求しない。
使われ方：Goerss–Jardine III §2、VIII §1。通常の交代 cochain との比較。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.NormalizedSimplicialCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]
  (K : SSet.{v}) (R M : C)

/-- 概要：反変 Hom 関手の正規化鎖での値は微分への前合成による cochain。
方針：各次数で恒等の加法同型を取り、隣接次数の微分を定義で比較する。
規約：これは通常の複体の厳密な同型。
使われ方：Goerss–Jardine III §2。生成子による正規化 cochain の表示への接続。 -/
def homComplexComparison :
    ContravariantChainHom.obj (K.normalizedChainComplex R) M ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homComplex K R M :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homComplex, CochainComplex.of_d]
      apply ConcreteCategory.hom_ext
      intro a
      rfl)

/-- 概要：通常の鎖複体の Hom と非退化単体の正規化 cochain はホモトピー同値。
方針：Mathlib の通常の正規化鎖の同値を Hom へ送り、二つの cochain 表示の同型に合成する。
規約：鎖のホモトピー同値そのものを使い、Hom の完全性は不要。
使われ方：Goerss–Jardine III §2、VIII §1。正規化 cochain の計算への入力。 -/
def normalizationHomotopyEquiv :
    HomotopyEquiv (ContravariantChainHom.obj (K.chainComplex R) M) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.complex K R M) :=
  (ContravariantChainHom.homotopyEquiv (K.homotopyEquivNormalizedChainComplex R) M).trans
    (HomotopyEquiv.ofIso (homComplexComparison K R M ≪≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.complexIso K R M))

end

end SerrePositivity.KST.Spectra.NormalizedSimplicialCochains

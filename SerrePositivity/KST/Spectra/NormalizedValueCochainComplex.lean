module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains
public import SerrePositivity.KST.Spectra.NormalizedCochainHomComparison

/-!
概要：通常の係数の元を値とする正規化 cochain 複体と正規化のホモトピー比較。
方針：Hom 係数を元の係数へ移した微分を複体へ束ね、正規化の同値に合成する。
規約：任意の加法群係数。幾何的微分との一致や塔の収束は含まない。
使われ方：Goerss–Jardine III §2、VIII §1。有理群 cochain の計算への比較先。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.NormalizedValueCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非退化単体上の通常の加法的係数の cochain 複体。
方針：退化面を零とする交代微分と二乗の零性を束ねる。
規約：係数の元をそのまま値とする。
使われ方：Goerss–Jardine III §2、VIII §1。通常の群 cochain と比較する複体。 -/
def complex (K : SSet.{u}) (M : AddCommGrpCat.{u}) : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (K.nonDegenerate n → M))
    (fun n ↦ AddCommGrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n))
    (fun n ↦ by
      apply ConcreteCategory.hom_ext
      intro a
      exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_comp K M n a)

/-- 概要：整数の単位係数からの Hom の正規化複体と元の係数の複体は同型。
方針：各次数の座標ごとの係数の加法同型と、微分の共役の定義を使う。
規約：整数係数の宇宙は ULift でそろえる。
使われ方：Goerss–Jardine III §2。正規化のホモトピー比較の係数表示。 -/
def complexIso (K : SSet.{u}) (M : AddCommGrpCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.complex K (AddCommGrpCat.of (ULift.{u} ℤ)) M ≅ complex K M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ AddEquiv.toAddCommGrpIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M n))
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.complex, complex, CochainComplex.of_d]
      apply ConcreteCategory.hom_ext
      intro a
      change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (i + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M i
          ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M i).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M i a))) =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (i + 1)
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M i a)
      rw [AddEquiv.symm_apply_apply])

/-- 概要：通常の整数鎖の Hom の cochain と元の係数の正規化 cochain はホモトピー同値。
方針：Mathlib の正規化鎖ホモトピー同値を反変 Hom に送り、係数の表示の同型に合成する。
規約：係数の入射性も有理性も不要。
使われ方：Goerss–Jardine III §2、VIII §1。群 cochain の代数的な比較への接続。 -/
def normalizationHomotopyEquiv (K : SSet.{u}) (M : AddCommGrpCat.{u}) :
    HomotopyEquiv
      (ContravariantChainHom.obj (K.chainComplex (AddCommGrpCat.of (ULift.{u} ℤ))) M)
      (complex K M) :=
  (NormalizedSimplicialCochains.normalizationHomotopyEquiv
    K (AddCommGrpCat.of (ULift.{u} ℤ)) M).trans (HomotopyEquiv.ofIso (complexIso K M))

end

end SerrePositivity.KST.Spectra.NormalizedValueCochains

module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains
public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
概要：正規化鎖複体の Hom と非退化単体上の cochain の複体同型。
方針：二つの微分の零合成から複体を作り、各次数の生成子の加法同型を束ねる。
規約：群の cohomology の消滅や幾何的微分との一致はここでは主張しない。
使われ方：Goerss–Jardine III §2、VIII §1。交代式を持つ比較先の複体。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.NormalizedSimplicialCochains
end SerrePositivity.KST.Spectra.NormalizedSimplicialCochains
namespace SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains
open SerrePositivity.KST.Spectra.NormalizedSimplicialCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]
  (K : SSet.{v}) (R M : C)

/-- 概要：正規化鎖複体の各鎖群から係数への Hom の cochain 複体。
方針：微分への前合成を加法群の圏の射へ束ねる。
規約：Hom の宇宙と単体集合の宇宙をそろえる。
使われ方：Goerss–Jardine III §2。正規化の通常の Hom による cochain。 -/
def homComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of ((K.normalizedChainComplex R).X n ⟶ M))
    (fun n ↦ AddCommGrpCat.ofHom (homDifferential K R M n))
    (fun n ↦ by
      apply ConcreteCategory.hom_ext
      intro a
      exact homDifferential_comp K R M n a)

/-- 概要：非退化単体上の係数の関数群の正規化 cochain 複体。
方針：移された交代微分とその二乗の零性を複体へ束ねる。
規約：退化面の寄与は零。
使われ方：Goerss–Jardine III §2、VIII §1。幾何的微分と比較する通常の複体。 -/
def complex : CochainComplex AddCommGrpCat.{v} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (K.nonDegenerate n → (R ⟶ M)))
    (fun n ↦ AddCommGrpCat.ofHom (differential K R M n))
    (fun n ↦ by
      apply ConcreteCategory.hom_ext
      intro a
      exact differential_comp K R M n a)

/-- 概要：正規化鎖群の Hom と非退化単体上の cochain は複体として同型。
方針：各次数の生成子の加法同型が微分の共役の定義により可換であることを使う。
規約：任意の前加法圏の係数の Hom 群。
使われ方：Goerss–Jardine III §2、VIII §1。通常の交代 cochain の比較。 -/
def complexIso : homComplex K R M ≅ complex K R M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ AddEquiv.toAddCommGrpIso (coefficientEquiv K R M n))
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      simp only [homComplex, complex, CochainComplex.of_d]
      apply ConcreteCategory.hom_ext
      intro a
      change coefficientEquiv K R M (i + 1)
        (homDifferential K R M i ((coefficientEquiv K R M i).symm
          (coefficientEquiv K R M i a))) =
        coefficientEquiv K R M (i + 1) (homDifferential K R M i a)
      rw [AddEquiv.symm_apply_apply])

end

end SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.complex := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complex

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.complexIso := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complexIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.homComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homComplex := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.homComplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.complex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.complex.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complex.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.complexIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.complexIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homComplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.homComplex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homComplex._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.homComplex._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homComplex.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.NormalizedSimplicialCochains.homComplex.eq_1

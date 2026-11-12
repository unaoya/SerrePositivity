module

public import SerrePositivity.KST.Spectra.SimplicialHomCochains
public import SerrePositivity.KST.Spectra.NormalizedCochainHomComparison

/-!
概要：全単体上の交代 cochain と非退化単体上の正規化 cochain のホモトピー同値。
方針：全単体の鎖の Hom を生成子で表示し、既存の正規化の同値に合成する。
規約：係数の完全性や入射性は不要。
使われ方：Goerss–Jardine III §2、VIII §2。群 cochain の正規化の比較。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialHomCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]
  (K : SSet.{v}) (R M : C)

/-- 概要：通常の鎖複体の Hom は全単体上の関数の交代 cochain 複体。
方針：各次数の余積の生成子への制限と、鎖の生成子の交代微分式を使う。
規約：Hom の微分への前合成と通常の交代微分を照合する。
使われ方：Goerss–Jardine III §2。正規化比較を全単体の cochain へ移す。 -/
def homComplexComparison : ContravariantChainHom.obj (K.chainComplex R) M ≅ complex K R M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ AddEquiv.toAddCommGrpIso (coefficientEquiv K R M n))
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      apply ConcreteCategory.hom_ext
      intro a
      funext s
      change (complex K R M).d i (i + 1) (coefficientEquiv K R M i a) s =
        K.ιChainComplex s ≫ ((K.chainComplex R).d (i + 1) i ≫ a)
      rw [differential_apply, ← Category.assoc, K.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
      rfl)

/-- 概要：全単体の通常の交代 cochain と非退化単体の正規化 cochain はホモトピー同値。
方針：全単体の鎖の Hom の比較を逆にし、Mathlib の正規化に由来する cochain の同値へ合成する。
規約：通常の複体のホモトピー同値であり、Tot の比較を主張しない。
使われ方：Goerss–Jardine III §2、VIII §2。正規化群 cochain の cohomology の入力。 -/
def normalizationHomotopyEquiv :
    HomotopyEquiv (complex K R M) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.complex K R M) :=
  (HomotopyEquiv.ofIso (homComplexComparison K R M).symm).trans
    (NormalizedSimplicialCochains.normalizationHomotopyEquiv K R M)

end

end SerrePositivity.KST.Spectra.SimplicialHomCochains

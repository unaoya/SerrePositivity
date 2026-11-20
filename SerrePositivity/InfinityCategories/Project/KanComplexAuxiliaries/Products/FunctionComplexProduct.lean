module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SimplicialFunctionComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：関数複体は定値な族の通常の積である。
方針：座標の評価と関数への持ち上げによる普遍性を使う。
規約：添字集合の有限性も係数の Kan 性も要求しない。
使われ方：Goerss–Jardine I §7、VIII §1。セルの Hom の積を関数複体へ移す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.SimplicialFunctionComplex
end SerrePositivity.KST.Spectra.SimplicialFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.SimplicialFunctionComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fan (S : Type u) (X : SSet.{u}) : Fan (fun (_ : S) ↦ X) :=
  Fan.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X)

/-- 概要：座標評価の fan は積の普遍性を持つ。
方針：射の族を lift し、各評価で一意性を検査する。
規約：対象は単体集合の具体的な関数複体。
使われ方：Goerss–Jardine I §7、VIII §1。積の群の具体的な関数表示。 -/
def fanIsLimit (S : Type u) (X : SSet.{u}) : IsLimit (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fan S X) :=
  Fan.IsLimit.mk _ (fun s ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun j ↦ s.proj j))
    (fun _ _ ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval _ _)
    (fun s m hm ↦ by
      apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
      intro j
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval]
      exact hm j)

/-- 概要：定値な族の選択された積と関数複体の標準同型。
方針：積の錐の一意性を使う。
規約：順射の各座標は対応する積の射影。
使われ方：Goerss–Jardine VIII §1。写像空間の積の具体化。 -/
noncomputable def productIso (S : Type u) (X : SSet.{u}) :
    (∏ᶜ fun (_ : S) ↦ X) ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X :=
  (productIsProduct _).conePointUniqueUpToIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fanIsLimit S X)

@[reassoc (attr := simp)]
lemma productIso_hom_eval (S : Type u) (X : SSet.{u}) (s : S) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.productIso S X).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S X s = Pi.π (fun (_ : S) ↦ X) s :=
  (productIsProduct _).conePointUniqueUpToIso_hom_comp (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fanIsLimit S X) (Discrete.mk s)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

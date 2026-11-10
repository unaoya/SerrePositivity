module

public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：直接定義の slice から太い slice への比較と任意パラメーターでの表示。
方針：普遍錐を fat join の比較で前合成して太い slice へ curry する。
規約：既存の slice の定義は維持する。
使われ方：Kerodon Proposition 4.6.4.19 の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：slice の普遍錐から太い slice への比較射。
方針：太い join の比較で普遍錐を前合成し、太い slice の普遍性で curry する。
規約：図式 p を厳密に固定する。
使われ方：Kerodon Proposition 4.6.4.19 の対角比較。 -/
@[kerodon 02GH]
noncomputable def sliceLaxMap {K X : SSet.{u}} (p : K ⟶ X) : sliceOver p ⟶ laxSlice p :=
  laxSliceCurry (fatJoinComparison (sliceOver p) K ≫ sliceOverUncurry (𝟙 (sliceOver p)))
    (by rw [← Category.assoc, fatJoinInr_comparison, sliceOverUncurry_fixed])

/-- 概要：slice から太い slice への比較後の uncurry は元の join の関手を太い比較で前合成したもの。
方針：curry の逆則、比較の自然性、slice の普遍性の自然性を組み合わせる。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の任意の関手の比較。 -/
lemma laxSliceUncurry_comp_sliceLaxMap {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) :
    laxSliceUncurry (f ≫ sliceLaxMap p) = fatJoinComparison A K ≫ sliceOverUncurry f := by
  rw [laxSliceUncurry_precomp, sliceLaxMap, laxSliceUncurry_curry,
    ← Category.assoc, fatJoinComparison_naturality]
  rw [Category.assoc, ← sliceOverUncurry_precomp, Category.comp_id]

/-- 概要：slice の比較は固定図式上の関手の頂点の比較と整合する。
方針：uncurry の比較を関手頂点へ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の同型類の比較。 -/
lemma sliceLaxMap_fixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) :
    (fixedDiagramPre (joinInr A K) (fatJoinInr A K) (fatJoinComparison A K)
      (fatJoinInr_comparison A K) p).app (Opposite.op ⦋0⦌) (sliceOverFixedDiagramVertex f) =
        laxSliceFixedDiagramVertex (f ≫ sliceLaxMap p) := by
  apply Subtype.ext
  change functorVertex (fatJoinComparison A K ≫ sliceOverUncurry f) =
    functorVertex (laxSliceUncurry (f ≫ sliceLaxMap p))
  rw [laxSliceUncurry_comp_sliceLaxMap]

/-- 概要：slice から太い slice への比較は任意のパラメーターの関手の同型を反映する。
方針：固定図式上の fat join 比較の同値による反映と二つの slice の同型判定を使う。
規約：X は quasicategory、パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の同型類の単射性。 -/
lemma nonempty_functorIso_of_sliceLaxMap {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (f g : A ⟶ sliceOver p)
    (e : FunctorIso (f ≫ sliceLaxMap p) (g ≫ sliceLaxMap p)) : Nonempty (FunctorIso f g) := by
  obtain ⟨et⟩ := nonempty_laxSliceFixedDiagramVertexIso_of_functorIso e
  let q := fixedDiagramPre (joinInr A K) (fatJoinInr A K) (fatJoinComparison A K)
    (fatJoinInr_comparison A K) p
  have he : IsQCatEquivalence q := isQCatEquivalence_fixedDiagramPre
    (joinInr A K) (fatJoinInr A K) (fatJoinComparison A K) (fatJoinInr_comparison A K) p
    (isPrecompositionEquivalence_fatJoinComparison A K)
  have ef : q.app (Opposite.op ⦋0⦌) (sliceOverFixedDiagramVertex f) =
      laxSliceFixedDiagramVertex (f ≫ sliceLaxMap p) := sliceLaxMap_fixedDiagramVertex f
  have eg : q.app (Opposite.op ⦋0⦌) (sliceOverFixedDiagramVertex g) =
      laxSliceFixedDiagramVertex (g ≫ sliceLaxMap p) := sliceLaxMap_fixedDiagramVertex g
  obtain ⟨es⟩ := he.vertexIso_of_map
    (eqToIso (congrArg SSet.HomotopyCategory.mk ef) ≪≫ et ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk eg)).symm)
  exact nonempty_functorIso_of_sliceOverFixedDiagramVertexIso f g es

end SerrePositivity.InfinityCategories

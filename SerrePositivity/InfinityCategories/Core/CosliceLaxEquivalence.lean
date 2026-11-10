module
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonEpi
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Core.FatJoinGeneralComparison
public import SerrePositivity.InfinityCategories.Core.FixedDiagramPrecomposition
public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinTensor
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Core.CoconeFixedComparison
public import SerrePositivity.InfinityCategories.Core.CosliceFixedDiagramIso
public import SerrePositivity.InfinityCategories.Core.LaxCoslice
public import SerrePositivity.InfinityCategories.Core.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUncurry
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUniversal
public import Mathlib.Tactic.CrossRefAttribute

/-! # Coslice と太い coslice の比較同値

概要：直接定義した coslice と太い coslice は quasicategory として同値。
方針：任意のパラメーターで固定図式上の関手の同型類を比較し、逆射を選ぶ。
規約：既存の coslice の定義は維持する。使われ方：余錐の族の比較と相対充填。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice への族と固定左図式上の余錐の頂点は同値。
方針：coslice の普遍性と固定図式の関手頂点の表示を合成する。
規約：任意のパラメーター。使われ方：比較同値の同型類の全射性。 -/
def sliceUnderFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceUnder p) ≃ (vertexFiber ((pre (joinInl K A)).app X) (functorVertex p)) _⦋0⦌ :=
  (sliceUnderEquiv p).trans (fixedDiagramVertexEquiv (joinInl K A) p)

/-- 概要：太い coslice への族と固定左図式上の太い余錐の頂点は同値。
方針：太い coslice の普遍性と固定図式の関手頂点の表示を合成する。
規約：任意のパラメーター。使われ方：比較同値の同型類の全射性。 -/
def laxCosliceFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ laxCoslice p) ≃ (vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p)) _⦋0⦌ :=
  (laxCosliceHomEquiv p A).trans (fixedDiagramVertexEquiv (fatJoinInl K A) p)

/-- 概要：coslice の普遍余錐を太い coslice の族にする比較射。
方針：fat join 比較で普遍余錐を前合成し、太い coslice に curry する。
規約：左図式を固定する。使われ方：余錐の模型の比較同値。 -/
@[kerodon 02GH]
noncomputable def cosliceLaxMap {K X : SSet.{u}} (p : K ⟶ X) : sliceUnder p ⟶ laxCoslice p :=
  laxCosliceCurry (fatJoinComparison K (sliceUnder p) ≫ sliceUnderUncurry (𝟙 (sliceUnder p)))
    (by rw [← Category.assoc, fatJoinInl_comparison, sliceUnderUncurry_fixed])

/-- 概要：slice から太い coslice への比較後の uncurry は元の join の関手を太い比較で前合成したもの。
方針：curry の逆則、比較の自然性、slice の普遍性の自然性を組み合わせる。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の任意の関手の比較。 -/
lemma laxCosliceUncurry_comp_cosliceLaxMap {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) :
    laxCosliceUncurry (f ≫ cosliceLaxMap p) = fatJoinComparison K A ≫ sliceUnderUncurry f := by
  rw [laxCosliceUncurry_precomp, cosliceLaxMap, laxCosliceUncurry_curry,
    ← Category.assoc, fatJoinComparison_naturality]
  rw [Category.assoc, ← sliceUnderUncurry_precomp, Category.comp_id]

/-- 概要：slice の比較は固定図式上の関手の頂点の比較と整合する。
方針：uncurry の比較を関手頂点へ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の同型類の比較。 -/
lemma cosliceLaxMap_fixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) :
    (fixedDiagramPre (joinInl K A) (fatJoinInl K A) (fatJoinComparison K A)
      (fatJoinInl_comparison K A) p).app (Opposite.op ⦋0⦌) (sliceUnderFixedDiagramVertex f) =
        laxCosliceFixedDiagramVertex (f ≫ cosliceLaxMap p) := by
  apply Subtype.ext
  change functorVertex (fatJoinComparison K A ≫ sliceUnderUncurry f) =
    functorVertex (laxCosliceUncurry (f ≫ cosliceLaxMap p))
  rw [laxCosliceUncurry_comp_cosliceLaxMap]

/-- 概要：slice から太い coslice への比較は任意のパラメーターの関手の同型を反映する。
方針：固定図式上の fat join 比較の同値による反映と二つの slice の同型判定を使う。
規約：X は quasicategory、パラメーター A は任意。
使われ方：Kerodon Proposition 4.6.4.19 の同型類の単射性。 -/
lemma nonempty_functorIso_of_cosliceLaxMap {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (f g : A ⟶ sliceUnder p)
    (e : FunctorIso (f ≫ cosliceLaxMap p) (g ≫ cosliceLaxMap p)) : Nonempty (FunctorIso f g) := by
  obtain ⟨et⟩ := nonempty_laxCosliceFixedDiagramVertexIso_of_functorIso e
  let q := fixedDiagramPre (joinInl K A) (fatJoinInl K A) (fatJoinComparison K A)
    (fatJoinInl_comparison K A) p
  have he : IsQCatEquivalence q := isQCatEquivalence_fixedDiagramPre
    (joinInl K A) (fatJoinInl K A) (fatJoinComparison K A) (fatJoinInl_comparison K A) p
    (isPrecompositionEquivalence_fatJoinComparison K A)
  have ef : q.app (Opposite.op ⦋0⦌) (sliceUnderFixedDiagramVertex f) =
      laxCosliceFixedDiagramVertex (f ≫ cosliceLaxMap p) := cosliceLaxMap_fixedDiagramVertex f
  have eg : q.app (Opposite.op ⦋0⦌) (sliceUnderFixedDiagramVertex g) =
      laxCosliceFixedDiagramVertex (g ≫ cosliceLaxMap p) := cosliceLaxMap_fixedDiagramVertex g
  obtain ⟨es⟩ := he.vertexIso_of_map
    (eqToIso (congrArg SSet.HomotopyCategory.mk ef) ≪≫ et ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk eg)).symm)
  exact nonempty_functorIso_of_sliceUnderFixedDiagramVertexIso f g es


/-- 概要：太い coslice の族は直接定義の coslice からの族と同型。
方針：固定図式上の fat join 比較の逆を任意のパラメーターで選ぶ。
規約：値域は quasicategory。使われ方：比較同値の逆関手。 -/
lemma exists_functorIso_comp_cosliceLaxMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A : SSet.{u}) (a : A ⟶ laxCoslice p) :
    ∃ f : A ⟶ sliceUnder p, Nonempty (FunctorIso (f ≫ cosliceLaxMap p) a) := by
  let q := fixedDiagramPre (joinInl K A) (fatJoinInl K A) (fatJoinComparison K A)
    (fatJoinInl_comparison K A) p
  have he : IsQCatEquivalence q := isQCatEquivalence_fixedDiagramPre
    (joinInl K A) (fatJoinInl K A) (fatJoinComparison K A) (fatJoinInl_comparison K A) p
    (isPrecompositionEquivalence_fatJoinComparison K A)
  let e := he.choose
  let y := laxCosliceFixedDiagramVertex a
  let v := e.inv.app (Opposite.op ⦋0⦌) y
  let f := (sliceUnderFixedDiagramVertexEquiv p A).symm v
  have hv : sliceUnderFixedDiagramVertex f = v :=
    (sliceUnderFixedDiagramVertexEquiv p A).apply_symm_apply v
  have hq : q.app (Opposite.op ⦋0⦌) v = laxCosliceFixedDiagramVertex (f ≫ cosliceLaxMap p) := by
    rw [← hv]
    exact cosliceLaxMap_fixedDiagramVertex f
  have et := FunctorIso.app e.invHomIso y
  change VertexIso (X := vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p))
    (q.app (Opposite.op ⦋0⦌) v) y at et
  refine ⟨f, ?_⟩
  apply nonempty_functorIso_of_laxCosliceFixedDiagramVertexIso
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hq)).symm ≪≫ et

/-- 概要：直接定義の coslice から太い coslice への比較は quasicategory の同値。
方針：恒等関手の同型類の逆像から逆関手を選び、同型の反映で他方の逆合成を同定する。
規約：X は quasicategory、K は任意、追加の有限性・非空性は不要。
使われ方：Kerodon Proposition 4.6.4.19 の太い coslice の比較。 -/
@[kerodon 01KU, kerodon 02VT]
lemma isQCatEquivalence_cosliceLaxMap {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    IsQCatEquivalence (cosliceLaxMap p) := by
  obtain ⟨g, ⟨eg⟩⟩ := exists_functorIso_comp_cosliceLaxMap p (laxCoslice p) (𝟙 (laxCoslice p))
  have ep : FunctorIso ((cosliceLaxMap p ≫ g) ≫ cosliceLaxMap p)
      ((𝟙 (sliceUnder p)) ≫ cosliceLaxMap p) := by
    have et := FunctorIso.precomp eg (cosliceLaxMap p)
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using et
  have eu := nonempty_functorIso_of_cosliceLaxMap (cosliceLaxMap p ≫ g) (𝟙 (sliceUnder p)) ep
  exact ⟨g, eu, ⟨eg⟩⟩


end SerrePositivity.InfinityCategories

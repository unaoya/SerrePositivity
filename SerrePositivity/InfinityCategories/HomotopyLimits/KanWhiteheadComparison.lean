module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanComparisonFibers
public import SerrePositivity.InfinityCategories.Kan.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.F1.Pointed.MonoRightHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Pointed.PointedKanWhitehead
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：Kan 複体の実際のホモトピー同値と全基点 π_* 同型を空の対象も含めて接続する。
方針：可逆 path 置換の二つの射影と、頂点を選んだ点つき Whitehead の定理を使う。
規約：空の始域の場合は π₀ の全射性を明示して標的も空であることを確認する。
使われ方：Goerss–Jardine I §§7–8、Kerodon 7.5.4.6、導来 fiber の実際の比較射の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Kan 複体間の射の可逆 path 置換の全空間は Kan。
方針：元の始域への自明 Kan fibration と始域の Kan 性を使う。
規約：元の射に fibration 性を要求しない。
使われ方：path 置換の同値性と全基点 π_* 同型性の比較。 -/
instance kanEquivalencePathReplacement_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) : KanComplex (equivalencePathReplacement f) := by
  have : Fibration (equivalencePathReplacementProjection f) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    intro A B j hj
    exact TrivialKanFibration.mem (p := equivalencePathReplacementProjection f) j
      (J_le_monomorphisms _ hj)
  exact isFibrant_of_fibration (equivalencePathReplacementProjection f)

/-- 概要：Kan 複体間の実際のホモトピー同値は全基点・全自然数次数の π_* 同型。
方針：path 置換の二つの射影の全ての単射への RLP と定値 path の厳密な分解を使う。
規約：元の始域の頂点や非空性を仮定しない。
使われ方：実際の同値性を既存の Kan fibration の fiber の全次数比較へ渡す。 -/
lemma kanPiIsomorphism_of_homotopyEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (he : IsSimplicialHomotopyEquivalence f) :
    KanPiIsomorphism f := by
  have : TrivialKanFibration (equivalencePathReplacementMap f) :=
    he.isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  have hr : KanPiIsomorphism (equivalencePathReplacementProjection f) :=
    kanPiIsomorphism_of_monoRight _ (TrivialKanFibration.mem (p := _))
  have hp : KanPiIsomorphism (equivalencePathReplacementMap f) :=
    kanPiIsomorphism_of_monoRight _ (TrivialKanFibration.mem (p := _))
  have hu : KanPiIsomorphism (equivalencePathReplacementSection f) := by
    apply KanPiIsomorphism.of_comp (g := equivalencePathReplacementProjection f) _ hr
    rw [equivalencePathReplacementSection_projection]
    exact KanPiIsomorphism.id X
  have h := hu.comp hp
  rw [equivalencePathReplacementSection_map] at h
  exact h

/-- 概要：源の頂点を持つ Kan 複体間の全基点 π_* 同型は実際のホモトピー同値。
方針：指定頂点を基点にして点つき Whitehead を適用し、基点条件を忘れる。
規約：元の射の fibration 性は要求しない。
使われ方：非空な fiber の全基点 π_* 比較を実際の同値へ移す。 -/
lemma homotopyEquivalence_of_kanPiIsomorphism_of_vertex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (hf : KanPiIsomorphism f) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence f := by
  let A := PointedSimplicialSet.ofVertex X x
  let B := PointedSimplicialSet.ofVertex Y (f.app _ x)
  let fp : A ⟶ B := Under.homMk f (by
    change SSet.const x ≫ f = SSet.const (f.app _ x)
    rw [SSet.const_comp])
  have : KanComplex A.right := inferInstanceAs (KanComplex X)
  have : KanComplex B.right := inferInstanceAs (KanComplex Y)
  obtain ⟨g, ⟨H, _⟩, ⟨K, _⟩⟩ := exists_pointedHomotopyInverse fp hf
  change SSet.Homotopy (𝟙 X) (f ≫ g.right) at H
  change SSet.Homotopy (𝟙 Y) (g.right ≫ f) at K
  have he : IsQCatEquivalence f := ⟨g.right,
    ⟨(functorIsoOfSimplicialHomotopy H).symm⟩, ⟨(functorIsoOfSimplicialHomotopy K).symm⟩⟩
  exact he.isSimplicialHomotopyEquivalence

/-- 概要：Kan 複体間の全基点 π_* 同型と π₀ の全射性は実際のホモトピー同値を与える。
方針：源に頂点があれば点つき Whitehead を使い、なければ標的も空であることを確認する。
規約：空の fiber の全基点条件だけで同値と結論しない。
使われ方：任意の底頂点上の fiber の比較で空の fiber を含める。 -/
lemma homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (hf : KanPiIsomorphism f)
    (h₀ : Function.Surjective (mapπ₀ f)) : IsSimplicialHomotopyEquivalence f := by
  classical
  by_cases hx : Nonempty (X _⦋0⦌)
  · exact homotopyEquivalence_of_kanPiIsomorphism_of_vertex f hf (Classical.choice hx)
  · have hY : ∀ y : Y _⦋0⦌, False := by
      intro y
      obtain ⟨a, _ha⟩ := h₀ (π₀.mk y)
      obtain ⟨x, _hx⟩ := π₀.mk_surjective a
      exact hx ⟨x⟩
    have (m : SimplexCategoryᵒᵖ) : IsEmpty (Y.obj m) := by
      obtain ⟨⟨n⟩⟩ := m
      exact ⟨fun s ↦ hY ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm 0))⟩
    have (m : SimplexCategoryᵒᵖ) : IsEmpty (X.obj m) := Function.isEmpty (f.app m)
    have : IsIso f := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro m
      rw [CategoryTheory.isIso_iff_bijective]
      exact ⟨fun a ↦ isEmptyElim a, fun b ↦ isEmptyElim b⟩
    exact homotopyEquivalence_of_isIso f

end
end SerrePositivity.InfinityCategories.HomotopyLimits

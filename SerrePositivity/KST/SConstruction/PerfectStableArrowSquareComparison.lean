module
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ArrowIsoFromCommutingEdges

/-!
概要：完全射の全自然な可換比較を、Cat^perf 内の区間図式全体の比較へ運ぶ。
方針：同じ射の類の合成則で可換式を回収し、指定可逆二成分で実区間を比較する。
規約：全関手同型を保持し、Verdier 商や局所化の新しい API は作らない。
使われ方：D2 の全対角・全 cone 比較から実右面の指定辺比較を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {A B C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
  (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C) (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B D)
  (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f.hom ≫ b.hom) (a.hom ≫ g.hom))
include e

/-- 概要：完全射の全自然比較は同じ Cat^perf 射の四辺可換式を与える。
方針：同じ完全合成の類と全関手同型不変性を使う。
規約：元四射を保持。使われ方：区間全比較の指定端点可換条件。 -/
lemma perfectStableHoArrow_square_eq_of_functorIso :
    perfectStableHoArrow f hA hB ≫ perfectStableHoArrow b hB hD =
      perfectStableHoArrow a hA hC ≫ perfectStableHoArrow g hC hD := by
  let F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A D := ⟨f.hom ≫ b.hom,
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ f.isExact b.isExact⟩
  let G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A D := ⟨a.hom ≫ g.hom,
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ a.isExact g.isExact⟩
  have hf : perfectStableHoArrow F hA hD =
      perfectStableHoArrow f hA hB ≫ perfectStableHoArrow b hB hD :=
    perfectStableHoArrow_comp f b hA hB hD
  have hg : perfectStableHoArrow G hA hD =
      perfectStableHoArrow a hA hC ≫ perfectStableHoArrow g hC hD :=
    perfectStableHoArrow_comp a g hA hC hD
  have he : perfectStableHoArrow F hA hD = perfectStableHoArrow G hA hD :=
    perfectStableHoArrow_eq_of_functorIso (F := F) (G := G) hA hD e
  exact hf.symm.trans (he.trans hg)

/-- 概要：全自然な可換比較と可逆二成分から、元 Cat^perf 辺の区間全比較を構成できる。
方針：同じ四辺可換式を既存の区間全比較の存在定理へ渡す。
規約：端点だけの同型ではない。使われ方：実右面の包含・商境界の指定比較。 -/
lemma nonempty_perfectStableArrowFunctorIso_of_equivalences
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence a.hom) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence b.hom) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (perfectStableArrow f hA hB).edge)
      (SSet.yonedaEquiv.symm (perfectStableArrow g hC hD).edge)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nonempty_arrowFunctorIso_of_comm
    (perfectStableArrow f hA hB).toTruncated (perfectStableArrow g hC hD).toTruncated
    (perfectStableArrow a hA hC).toTruncated (perfectStableArrow b hB hD).toTruncated
  · exact perfectStableHoArrow_isIso_of_isQCatEquivalence a hA hC ha
  · exact perfectStableHoArrow_isIso_of_isQCatEquivalence b hB hD hb
  · exact perfectStableHoArrow_square_eq_of_functorIso f g a b hA hB hC hD e
/-- 概要：可換四辺の実ホモトピーと同じ二端点の全経路を保持する。
方針：区間全比較を構成する実四角形を指定する。
規約：比較の可逆性は端点の可逆性から検出。使われ方：上下二胞体の同時貼り合わせ。 -/
structure PerfectStableArrowSquareWitness where
  homotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (perfectStableArrow f hA hB).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow g hC hD).edge)
  source_path : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ homotopy.h =
    CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
      SSet.yonedaEquiv.symm (perfectStableArrow a hA hC).edge
  target_path : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ homotopy.h =
    CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
      SSet.yonedaEquiv.symm (perfectStableArrow b hB hD).edge

/-- 概要：元の全自然比較から同じ両端経路を保つ実四角形を構成できる。
方針：四辺可換式を元の指定四辺の実ホモトピーへ運ぶ。
規約：端点経路を存在型内に保持。使われ方：同じ頂点成分を持つ指定境界の選択。 -/
lemma nonempty_perfectStableArrowSquareWitness :
    Nonempty (PerfectStableArrowSquareWitness f g a b hA hB hC hD) := by
  obtain ⟨H, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.exists_arrowHomotopy_of_homMk_comm
    (perfectStableArrow f hA hB).toTruncated (perfectStableArrow g hC hD).toTruncated
    (perfectStableArrow a hA hC).toTruncated (perfectStableArrow b hB hD).toTruncated
    (perfectStableHoArrow_square_eq_of_functorIso f g a b hA hB hC hD e)
  exact ⟨⟨H, h₀, h₁⟩⟩

/-- 概要：同じ全自然比較から指定二端点の実ホモトピーを選ぶ。
方針：元四辺の端点式も含む証人を選択する。
規約：端点式を捨てない。使われ方：実右面の指定辺比較と全二胞体の接続。 -/
def perfectStableArrowSquareWitness : PerfectStableArrowSquareWitness f g a b hA hB hC hD :=
  Classical.choice (nonempty_perfectStableArrowSquareWitness f g a b hA hB hC hD e)

omit e
namespace PerfectStableArrowSquareWitness
variable {f g a b hA hB hC hD}
variable (w : PerfectStableArrowSquareWitness f g a b hA hB hC hD)

/-- 概要：元実ホモトピーは可逆な指定二端点から全比較として可逆。
方針：既存の両端点による区間可逆性を使う。
規約：同じホモトピーを保持。使われ方：指定辺全比較の可逆性。 -/
lemma isInvertible
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow a hA hC).toTruncated)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow b hB hD).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy w.homotopy) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths w.homotopy
    (perfectStableArrow a hA hC).toTruncated (perfectStableArrow b hB hD).toTruncated
    ha hb w.source_path w.target_path

/-- 概要：同じ実四角形は二端点の可逆性から元区間全比較を与える。
方針：元ホモトピーの辺の類を同型にする。
規約：同じホモトピーを使用。使われ方：指定端点経路を回収できる辺比較。 -/
def comparison
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow a hA hC).toTruncated)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow b hB hD).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (perfectStableArrow f hA hB).edge)
      (SSet.yonedaEquiv.symm (perfectStableArrow g hC hD).edge) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy w.homotopy)) (w.isInvertible ha hb)

/-- 概要：同じ指定二端点同値を持つ実四角形の区間全比較。
方針：二完全同値の Cat^perf 辺の可逆性を代入する。
規約：元ホモトピーと端点式を保持。使われ方：実右面の包含・商の同じ全比較。 -/
def comparisonOfEquivalences (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence a.hom) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence b.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (perfectStableArrow f hA hB).edge)
      (SSet.yonedaEquiv.symm (perfectStableArrow g hC hD).edge) :=
  w.comparison (perfectStableHoArrow_isIso_of_isQCatEquivalence a hA hC ha)
    (perfectStableHoArrow_isIso_of_isQCatEquivalence b hB hD hb)
end PerfectStableArrowSquareWitness
end SerrePositivity.KST.SConstruction

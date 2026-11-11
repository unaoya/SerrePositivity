module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinHomotopyFixed

/-!
概要：標準単体の旗の解像の射影は前合成による同値を与える。
方針：区間の切断の像を固定する変形と、全頂点がその像に入ることを使う。
規約：旗の解像自体の quasicategory 性は仮定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の比較の圏的な同値性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間から作った旗を区間化しても変わらない。
方針：区間の最大元から元の頂点列を回収する。
規約：値域の標準単体の次数は固定する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断の像の固定性。 -/
lemma CoherentResolutionFlag.intervalHull_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f).intervalHull = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f).maxAt, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f).maxAt_monotone⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f
  congr 1
  apply OrderHom.ext
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.maxAt_interval f i

/-- 概要：区間から作った旗は変形中固定される。
方針：区間化で不変な旗の固定性を使う。
規約：単位区間の全単体に適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断上で相対的な変形。 -/
lemma CoherentResolutionFlag.deform_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f).deform t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval f).deform_intervalHull t
  rwa [CoherentResolutionFlag.intervalHull_interval] at h

/-- 概要：零次元の旗は既に区間の旗。
方針：唯一の集合は始点の一点集合なので、区間化の最初の集合と一致する。
規約：全頂点に関する等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断の頂点での全射性。 -/
lemma CoherentResolutionFlag.intervalHull_vertex {n : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n 0) :
    F.intervalHull = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext F.intervalHull_start
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact F.intervalHull.first.trans
    ((congrArg (fun k ↦ ({k} : Finset _)) F.intervalHull_start).trans F.first.symm)

/-- 概要：区間の切断は全ての頂点に到達する。
方針：旗の頂点を射影して切断へ戻すと区間化となり、零次元では元に戻る。
規約：高次単体での全射性は主張しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、変形の全頂点での可逆性。 -/
lemma coherentResolutionSection_vertex_surjective (n : ℕ) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection.{u} n).app (Opposite.op ⦋0⦌)) := by
  intro F
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n).app _ F, ?_⟩
  apply ULift.ext
  exact F.down.intervalHull_vertex

/-- 概要：旗の変形は区間の切断の像を固定する。
方針：各単体において区間の旗の変形の固定性を使う。
規約：単位区間全体にわたる射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、頂点上のホモトピーの辺の可逆性。 -/
lemma coherentResolutionDeformation_section (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection.{u} n ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDeformation n =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  exact CoherentResolutionFlag.deform_interval x.1.down.toOrderHom x.2.down.toOrderHom

/-- 概要：旗の解像の変形は各頂点で可逆な辺を与える。
方針：頂点を切断の像で表示し、その像上で固定されるホモトピーの補題を使う。
規約：旗の解像の quasicategory 性は不要。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、前合成による圏的同値の判定。 -/
lemma coherentResolutionHomotopy_vertex_isInvertible (n : ℕ)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomotopy n) F).toTruncated := by
  obtain ⟨s, rfl⟩ := coherentResolutionSection_vertex_surjective n F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyVertexEdge_isInvertible_of_fixed_map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomotopy n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n)
    (coherentResolutionDeformation_section n) s

/-- 概要：旗の解像の射影は任意の quasicategory への前合成で同値を与える。
方針：一方の合成の切断則と他方の合成への点ごとに可逆な変形に二対六則を適用する。
規約：解像の圏的な比較を IsPrecompositionEquivalence で表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の補助解像の同値。 -/
lemma coherentResolutionProjection_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection.{u} n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_composites
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n) (h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection_projection]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_of_homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomotopy n)
      (coherentResolutionHomotopy_vertex_isInvertible n)).mp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _)

/-- 概要：区間の切断も前合成による同値を与える。
方針：切断と射影の合成は恒等なので、射影の同値性を消去する。
規約：解像の quasicategory 性は要求しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体との比較の逆方向。 -/
lemma coherentResolutionSection_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection.{u} n) := by
  apply (coherentResolutionProjection_isPrecompositionEquivalence n).cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

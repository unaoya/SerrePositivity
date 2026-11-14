module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionCoproductGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionSequentialGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension

/-!
概要：標準単体上の自然な比較から任意の単体集合上の比較へのセルによる拡張。
方針：境界の次数による帰納、セルの族の coproduct、骨格の pushout と可算余極限を使う。
規約：二つの関手は単射と使用する連結な余極限を保つことを要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join 比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：自然な比較の同値条件は始域の対象の同型で不変。
方針：自然性の正方形と二つの関手が同型を保つことを使う。
規約：関手に単射や余極限の保存は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの表示の変更。 -/
lemma isPrecompositionEquivalence_natComponent_of_iso
    {F G : SSet.{u} ⥤ SSet.{u}} (t : F ⟶ G) {A B : SSet.{u}} (e : A ≅ B)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app B)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app A) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (F.mapIso e)).comp hB
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map e.hom ≫ t.app B) at h
  rw [t.naturality e.hom] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (G.mapIso e)).cancel_right h

/-- 概要：単射を含む pushout で自然な比較の同値条件を貼り合わせられる。
方針：二つの関手で写した pushout に一般の比較の貼り合わせを適用する。
規約：両関手は単射と pushout を保つ。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各骨格の貼り合わせ。 -/
lemma isPrecompositionEquivalence_natComponent_of_pushout
    {F G : SSet.{u} ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    {A B C D : SSet.{u}} {f : A ⟶ B} [Mono f] {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (h : IsPushout f g r s) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app A))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app B)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app D) := by
  have : Mono (F.map f) := F.map_mono _
  have : Mono (G.map f) := G.map_mono _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing (h.map F) (h.map G)
    (t.app A) (t.app B) (t.app C) (t.app D)
    (t.naturality f) (t.naturality g) (t.naturality r) (t.naturality s) hA hB hC

/-- 概要：次元が n 未満の単体集合の n 骨格は全体。
方針：全ての非退化単体の次元が n 未満であることを使う。
規約：Mathlib の骨格は次元 n 未満を生成するもの。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の境界の帰納。 -/
lemma skeleton_eq_top_of_hasDimensionLT (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] :
    X.skeleton n = ⊤ := by
  apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ n).2
  intro d hd x _
  exact X.mem_skeleton x hd

/-- 概要：次元が n 未満なら初期対象に相対的な n 骨格は全体と同型。
方針：骨格が全体であることと部分複体の表示同型を使う。
規約：初期対象からの射を固定する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の境界の比較。 -/
noncomputable def initialSkeletonIso (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] :
    (skeletonOfMono (initial.to X) n : SSet.{u}) ≅ X :=
  Subcomplex.eqToIso (by
    change Subcomplex.range (initial.to X) ⊔ X.skeleton n = ⊤
    rw [skeleton_eq_top_of_hasDimensionLT X n, sup_top_eq]) ≪≫ Subcomplex.topIso X

/-- 概要：初期対象と全ての標準単体で同値条件を満たす自然な比較は全単体集合で満たす。
方針：境界の次数で帰納し、各骨格のセルの族を貼り、可算の骨格の余極限を取る。
規約：関手は単射、pushout、可算余極限、単体の宇宙 u の wide pushout を保つ。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の標準単体への還元。 -/
lemma isPrecompositionEquivalence_natComponent_of_stdSimplex
    {F G : SSet.{u} ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ G]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) F]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) G]
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (⊥_ SSet.{u})))
    (hstd : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (Δ[n] : SSet.{u})))
    (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app X) := by
  have hsk : ∀ n (Y : SSet.{u}),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (skeletonOfMono (initial.to Y) n : SSet.{u})) := by
    intro n
    induction n with
    | zero =>
      intro Y
      exact isPrecompositionEquivalence_natComponent_of_iso t (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso (initial.to Y)) h0
    | succ n ih =>
      intro Y
      let i : (⊥_ SSet.{u}) ⟶ Y := initial.to Y
      have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (boundary n : SSet.{u})) :=
        isPrecompositionEquivalence_natComponent_of_iso t
          (initialSkeletonIso (boundary n : SSet.{u}) n).symm (ih _)
      have hBoundaryFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
          (t.app (SSet.relativeCellComplexOfMono.sigmaBoundary i n)) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_coproduct_colimit
          (SSet.relativeCellComplexOfMono.Cell i n) t (fun _ ↦ (boundary n : SSet.{u})) h0 (fun _ ↦ hb)
      have hSimplexFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
          (t.app (SSet.relativeCellComplexOfMono.sigmaStdSimplex i n)) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_coproduct_colimit
          (SSet.relativeCellComplexOfMono.Cell i n) t (fun _ ↦ (Δ[n] : SSet.{u})) h0 (fun _ ↦ hstd n)
      exact isPrecompositionEquivalence_natComponent_of_pushout t
        (SSet.relativeCellComplexOfMono.isPushout i n).flip hBoundaryFamily hSimplexFamily (ih Y)
  let r := SSet.relativeCellComplexOfMono (initial.to X)
  have : ∀ n, Mono (r.F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    change Mono (SSet.relativeCellComplexOfMono.r (initial.to X) n)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_sequential_colimit t r.F ⟨X, r.incl⟩ r.isColimit
    (fun n ↦ hsk n X)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.2.2.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_natComponent_of_stdSimplex

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSkeletonColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：Over 圏上の自然な比較を標準単体上の比較から任意の対象へ拡張する。
方針：構造射を保ったセルの族、骨格の pushout、骨格列の余極限を使う。
規約：通常の単体集合を値とする二つの関手は単射と使用する余極限を保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の各単体での比較から全体への還元。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：Over 圏の単射に沿う pushout で自然な比較の同値条件を貼れる。
方針：両関手で写した pushout に比較の貼り合わせ判定を使う。
規約：比較の成分の単射性は不要。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底のセルを貼る段階。 -/
lemma isPrecompositionEquivalence_over_natComponent_of_pushout
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    {A B C D : Over S} {i : A ⟶ B} [Mono i] {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hp : IsPushout i g r s) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app A))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app B)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app D) := by
  have : Mono (F.map i) := F.map_mono _
  have : Mono (G.map i) := G.map_mono _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing (hp.map F) (hp.map G)
    (τ.app A) (τ.app B) (τ.app C) (τ.app D)
    (τ.naturality i) (τ.naturality g) (τ.naturality r) (τ.naturality s) hA hB hC

/-- 概要：骨格と各セルおよび境界の比較から次の骨格の比較が従う。
方針：構造射を保つ coproduct の比較を骨格の pushout に貼る。
規約：初期対象の比較も共通の貼り合わせ部分として仮定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の単体の次元に関する帰納。 -/
lemma isPrecompositionEquivalence_over_natComponent_skeleton_succ
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) F]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) G]
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (⊥_ (Over S))))
    {A X : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S) (d : ℕ)
    (hprev : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (τ.app (Over.mk ((skeletonOfMono i d).ι ≫ f))))
    (hboundary : ∀ c : Cell i d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (τ.app (Over.mk ((boundary d).ι ≫ c.map ≫ f))))
    (hcell : ∀ c : Cell i d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk (c.map ≫ f)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk ((skeletonOfMono i (d + 1)).ι ≫ f))) := by
  let a : Over S := Over.mk (l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f)
  let b₀ : Over S := Over.mk (b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f)
  let c₀ : Over S := Over.mk ((skeletonOfMono i d).ι ≫ f)
  let d₀ : Over S := Over.mk ((skeletonOfMono i (d + 1)).ι ≫ f)
  have hw : t i d ≫ (skeletonOfMono i d).ι ≫ f =
      l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f := by
    have h := congrArg (fun k : sigmaBoundary i d ⟶ (skeletonOfMono i (d + 1) : SSet.{u}) ↦
      k ≫ (skeletonOfMono i (d + 1)).ι ≫ f) (w i d)
    simp only [Category.assoc] at h
    rw [← Category.assoc (r i d) (skeletonOfMono i (d + 1)).ι f] at h
    simpa only [r, Subcomplex.homOfLE_ι] using h
  let u₀ : a ⟶ b₀ := Over.homMk (l i d) rfl
  let v₀ : a ⟶ c₀ := Over.homMk (t i d) hw
  let r₀ : b₀ ⟶ d₀ := Over.homMk (b i d) rfl
  let s₀ : c₀ ⟶ d₀ := Over.homMk (r i d) (by
    change r i d ≫ ((skeletonOfMono i (d + 1)).ι ≫ f) = (skeletonOfMono i d).ι ≫ f
    rw [← Category.assoc]
    rfl)
  have hp : IsPushout u₀ v₀ r₀ s₀ := by
    apply IsPushout.of_map_of_faithful (Over.forget S)
    exact (SSet.relativeCellComplexOfMono.isPushout i d).flip
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app a) := by
    have he : a.hom = Sigma.desc
        (fun c : Cell i d ↦ (boundary d).ι ≫ c.map ≫ f) := by
      apply Sigma.hom_ext
      intro c
      rw [Sigma.ι_comp_desc]
      change c.ιSigmaBoundary ≫ (l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f) = _
      simp only [← Category.assoc]
      rw [Cell.ι_l]
      simp only [Category.assoc]
      rw [reassoc_of% Cell.ι_b_ι c]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk a.hom))
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_coproduct_cocone (Cell i d) τ
      (fun c ↦ Over.mk ((boundary d).ι ≫ c.map ≫ f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOverSigmaCofan (fun _ : Cell i d ↦ (boundary d : SSet.{u})) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOverSigmaCofan_isColimit (fun _ : Cell i d ↦ (boundary d : SSet.{u})) _)
      h0 hboundary
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app b₀) := by
    have he : b₀.hom = Sigma.desc (fun c : Cell i d ↦ c.map ≫ f) := by
      apply Sigma.hom_ext
      intro c
      rw [Sigma.ι_comp_desc]
      change c.ιSigmaStdSimplex ≫ (b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f) = c.map ≫ f
      exact (reassoc_of% Cell.ι_b_ι c) f
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk b₀.hom))
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_coproduct_cocone (Cell i d) τ
      (fun c ↦ Over.mk (c.map ≫ f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOverSigmaCofan (fun _ : Cell i d ↦ (Δ[d] : SSet.{u})) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOverSigmaCofan_isColimit (fun _ : Cell i d ↦ (Δ[d] : SSet.{u})) _)
      h0 hcell
  have : Mono u₀.left := inferInstanceAs (Mono (l i d))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app d₀)
  have : Mono u₀ := Over.mono_of_mono_left _
  apply isPrecompositionEquivalence_over_natComponent_of_pushout τ hp hA hB
  exact hprev


/-- 概要：初期対象と全ての底上の標準単体での自然な比較から全ての構造射の比較が従う。
方針：各骨格を次元で帰納し、境界を小さい骨格から取り出し、骨格列の余極限へ貼る。
規約：標準単体の底への構造射は全て試験する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各単体への pullback による局所的な比較判定。 -/
lemma isPrecompositionEquivalence_over_natComponent_of_stdSimplex
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ G]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) F]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) G]
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (⊥_ (Over S))))
    (hstd : ∀ (d : ℕ) (p : (Δ[d] : SSet.{u}) ⟶ S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk p)))
    (X : SSet.{u}) (f : X ⟶ S) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk f)) := by
  have hsk : ∀ d (Y : SSet.{u}) (g : Y ⟶ S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
        (τ.app (Over.mk ((skeletonOfMono (initial.to Y) d).ι ≫ g))) := by
    intro d
    induction d with
    | zero =>
      intro Y g
      let q := (skeletonOfMono (initial.to Y) 0).ι ≫ g
      have hI : IsInitial (skeletonOfMono (initial.to Y) 0 : SSet.{u}) :=
        IsInitial.ofIso initialIsInitial (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso (initial.to Y)).symm
      have hO : IsInitial (Over.mk q) :=
        IsInitial.isInitialOfObj (Over.forget S) _ hI
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_iso τ
        (hO.uniqueUpToIso initialIsInitial) h0
    | succ d hd =>
      intro Y g
      have hb : ∀ p : (boundary d : SSet.{u}) ⟶ S,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (τ.app (Over.mk p)) := by
        intro p
        have : IsIso (skeletonOfMono (initial.to (boundary d : SSet.{u})) d).ι :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_initialSkeleton_ι_isIso (boundary d : SSet.{u}) d
        let e : Over.mk ((skeletonOfMono (initial.to (boundary d : SSet.{u})) d).ι ≫ p) ≅
            Over.mk p :=
          Over.isoMk (asIso (skeletonOfMono (initial.to (boundary d : SSet.{u})) d).ι) rfl
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_iso τ e.symm (hd _ p)
      apply isPrecompositionEquivalence_over_natComponent_skeleton_succ τ h0
        (initial.to Y) g d (hd Y g)
      · intro c
        exact hb _
      · intro c
        exact hstd d (c.map ≫ g)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_sequential_colimit τ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonDiagram (initial.to X) f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonCocone (initial.to X) f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonCocone_isColimit (initial.to X) f)
  intro d
  exact hsk d X f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

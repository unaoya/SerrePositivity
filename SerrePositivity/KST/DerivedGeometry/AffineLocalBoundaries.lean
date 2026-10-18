module

public import SerrePositivity.KST.DerivedGeometry.SheafLocalBoundaries
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：スペクトル上の加群層の局所境界表示を基本開へ細分する。
方針：基本開基底を使い、自然性で境界等式をさらに制限する。
規約：係数環とスペクトルの環を独立に扱う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の局所 Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R A : Type u} [Ring R] [CommRing A]

/--
概要：サイクル層の任意の切断は各点を含む基本開上で境界となる。
方針：局所全射性の近傍を基本開へ細分し、境界射の自然性を使う。
規約：境界を与える切断と基本開の包含を明示する。
使われ方：TT §3、Toën §3.2 のアフィン層コホモロジー比較。
-/
lemma affineSheafExact_basicOpenBoundary
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)))
    (hS : S.Exact) (U : Opens (PrimeSpectrum A))
    (z : S.cycles.obj.obj (.op U)) (x : PrimeSpectrum A) (hx : x ∈ U) :
    ∃ (a : A) (haU : basicOpen a ≤ U), x ∈ basicOpen a ∧
      ∃ y : S.X₁.obj.obj (.op (basicOpen a)),
        S.toCycles.hom.app (.op (basicOpen a)) y =
          S.cycles.obj.map (homOfLE haU).op z := by
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ :=
    sheafExact_localBoundary (R := R) (X := TopCat.of (PrimeSpectrum A)) S hS U z x hx
  obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ :=
    (isTopologicalBasis_basic_opens (R := A)).isOpen_iff.mp V.isOpen x hxV
  let h : basicOpen a ≤ V := haV
  refine ⟨a, h.trans hVU, hxa, S.X₁.obj.map (homOfLE h).op y, ?_⟩
  calc
    _ = S.cycles.obj.map (homOfLE h).op (S.toCycles.hom.app (.op V) y) := by
      exact congrArg (fun k : S.X₁.obj.obj (.op V) ⟶
        S.cycles.obj.obj (.op (basicOpen a)) => k y)
          (S.toCycles.hom.naturality (homOfLE h).op)
    _ = S.cycles.obj.map (homOfLE h).op
        (S.cycles.obj.map (homOfLE hVU).op z) := by rw [hy]
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl

/--
概要：準コンパクトな開上のサイクル切断は有限基本開被覆上で境界となる。
方針：各点で得た基本開の境界表示から有限部分被覆を選ぶ。
規約：有限被覆の各元で実際の境界切断を保持する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限 Čech 比較。
-/
lemma affineSheafExact_finiteBasicOpenBoundaries
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)))
    (hS : S.Exact) (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : S.cycles.obj.obj (.op U)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧
        ∀ i, ∃ y : S.X₁.obj.obj (.op (basicOpen (f i))),
          S.toCycles.hom.app (.op (basicOpen (f i))) y =
            S.cycles.obj.map (homOfLE (hf i)).op z := by
  classical
  have hex (x : U) := affineSheafExact_basicOpenBoundary S hS U z x.val x.property
  choose f hf hxf y hy using hex
  have hc : (U : Set (PrimeSpectrum A)) ⊆ ⋃ x : U, (basicOpen (f x) : Set _) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover
    (fun x : U => (basicOpen (f x) : Set _)) (fun _ => (basicOpen _).isOpen) hc
  refine ⟨s, fun i => f i.val, fun i => hf i.val, ?_, fun i => ⟨y i.val, hy i.val⟩⟩
  apply le_antisymm
  · exact iSup_le (fun i => hf i.val)
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, his⟩, hxi⟩

end SerrePositivity.KST.DerivedGeometry

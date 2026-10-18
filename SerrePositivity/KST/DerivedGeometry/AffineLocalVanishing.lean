module

public import SerrePositivity.KST.DerivedGeometry.SheafSectionCohomology
public import SerrePositivity.KST.DerivedGeometry.AffineLocalBoundaries

/-!
概要：切断コホモロジーの局所消滅を有限基本開被覆へまとめる。
方針：基本開基底による細分と準コンパクト性を使う。
規約：被覆の各元への実際の制限写像で零になることを証明する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限 Čech 比較。
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
概要：局所的に零となる前層の切断は基本開近傍でも零となる。
方針：零となる近傍を基本開へ細分し、制限の合成と零の保存を使う。
規約：層条件を仮定しない。
使われ方：TT §3、Toën §3.2 のコホモロジー類の局所消滅。
-/
lemma affinePresheaf_basicOpenVanishing
    (P : (Opens (PrimeSpectrum A))ᵒᵖ ⥤ ModuleCat.{u} R)
    (U : Opens (PrimeSpectrum A)) (z : P.obj (.op U))
    (hloc : ∀ x ∈ U, ∃ (V : Opens (PrimeSpectrum A)) (hVU : V ≤ U),
      x ∈ V ∧ P.map (homOfLE hVU).op z = 0)
    (x : PrimeSpectrum A) (hx : x ∈ U) :
    ∃ (a : A) (haU : basicOpen a ≤ U),
      x ∈ basicOpen a ∧ P.map (homOfLE haU).op z = 0 := by
  obtain ⟨V, hVU, hxV, hz⟩ := hloc x hx
  obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ :=
    (isTopologicalBasis_basic_opens (R := A)).isOpen_iff.mp V.isOpen x hxV
  let h : basicOpen a ≤ V := haV
  refine ⟨a, h.trans hVU, hxa, ?_⟩
  have he : P.map (homOfLE (h.trans hVU)).op =
      P.map (homOfLE hVU).op ≫ P.map (homOfLE h).op := by
    rw [← P.map_comp]
    rfl
  rw [he, ConcreteCategory.comp_apply, hz]
  exact map_zero _

/--
概要：準コンパクトな開上の局所零切断は有限基本開被覆上で零となる。
方針：各点の基本開近傍の消滅表示から有限部分被覆を選ぶ。
規約：被覆の各元の包含と制限による消滅を保持する。
使われ方：TT §3、Toën §3.2 の有限 Čech の局所消滅。
-/
lemma affinePresheaf_finiteBasicOpenVanishing
    (P : (Opens (PrimeSpectrum A))ᵒᵖ ⥤ ModuleCat.{u} R)
    (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : P.obj (.op U))
    (hloc : ∀ x ∈ U, ∃ (V : Opens (PrimeSpectrum A)) (hVU : V ≤ U),
      x ∈ V ∧ P.map (homOfLE hVU).op z = 0) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧ ∀ i, P.map (homOfLE (hf i)).op z = 0 := by
  classical
  have hex (x : U) := affinePresheaf_basicOpenVanishing P U z hloc x.val x.property
  choose f hf hxf hz using hex
  have hc : (U : Set (PrimeSpectrum A)) ⊆ ⋃ x : U, (basicOpen (f x) : Set _) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover
    (fun x : U => (basicOpen (f x) : Set _)) (fun _ => (basicOpen _).isOpen) hc
  refine ⟨s, fun i => f i.val, fun i => hf i.val, ?_, fun i => hz i.val⟩
  apply le_antisymm
  · exact iSup_le (fun i => hf i.val)
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, his⟩, hxi⟩

/--
概要：完全な加群層の短複体の切断コホモロジー類は有限基本開被覆上で零。
方針：証明済みの局所消滅を有限基本開細分の定理に適用する。
規約：コホモロジー類の各制限そのものが零になる。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の層コホモロジー比較。
-/
lemma affineSectionHomology_finiteBasicOpenVanishing
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)))
    (hS : S.Exact) (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : (sectionHomologyPresheaf (R := R) (X := TopCat.of (PrimeSpectrum A)) S).obj (.op U)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧
        ∀ i, (sectionHomologyPresheaf (R := R) (X := TopCat.of (PrimeSpectrum A)) S).map (homOfLE (hf i)).op z = 0 :=
  affinePresheaf_finiteBasicOpenVanishing (sectionHomologyPresheaf (R := R) (X := TopCat.of (PrimeSpectrum A)) S) U hU z
    (fun x hx => sectionHomologyPresheaf_locallyZero
      (X := TopCat.of (PrimeSpectrum A)) S hS U z x hx)

end SerrePositivity.KST.DerivedGeometry

module

public import SerrePositivity.KST.DerivedGeometry.SheafExtLocalVanishing

/-!
概要：正次数 Ext 類は準コンパクトなアフィン開の有限基本開被覆で零。
方針：実際の Ext 前層の局所消滅を基本開で細分して有限部分被覆を取る。
規約：係数環は非可換でもよく、Ext の存在は既証の instance を使う。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace PrimeSpectrum Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A]

/--
概要：局所的に零となる前層の切断は基本開近傍でも零となる。
方針：零となる近傍を基本開へ細分し、制限の合成と零の保存を使う。
規約：層条件を仮定しない。
使われ方：TT §3、Toën §3.2 のコホモロジー類の局所消滅。
-/
lemma affineAbPresheaf_basicOpenVanishing
    (P : (Opens (PrimeSpectrum A))ᵒᵖ ⥤ AddCommGrpCat.{u})
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
lemma affineAbPresheaf_finiteBasicOpenVanishing
    (P : (Opens (PrimeSpectrum A))ᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : P.obj (.op U))
    (hloc : ∀ x ∈ U, ∃ (V : Opens (PrimeSpectrum A)) (hVU : V ≤ U),
      x ∈ V ∧ P.map (homOfLE hVU).op z = 0) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧ ∀ i, P.map (homOfLE (hf i)).op z = 0 := by
  classical
  have hex (x : U) := affineAbPresheaf_basicOpenVanishing P U z hloc x.val x.property
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
概要：アフィン空間上の固定環加群層の Ext は同じ宇宙で存在する。
方針：TopCat の表示を明示して構成済みの一般の存在定理を適用する。
規約：存在を新たな仮定にしない。
使われ方：TT §3、Toën §3.2 のアフィン Ext。
-/
instance affineModuleSheaf_hasExt {R : Type u} [Ring R] :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)) :=
  moduleSheaf_hasExt (R := R) (X := TopCat.of (PrimeSpectrum A))

/--
概要：自由層からの正次数 Ext の類は有限基本開被覆で制限が零となる。
方針：injective 分解から証明した局所消滅へ準コンパクト性を適用する。
規約：被覆の各元への実際の Ext の前合成の消滅を保持する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型帰納。
-/
lemma moduleSheafExt_finiteBasicOpenVanishing {R : Type u} [Ring R]
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R))
    (n : ℕ) (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (α : Ext ((freeModuleSheafOnOpen R (TopCat.of (PrimeSpectrum A))).obj U) F (n + 1)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧ ∀ i,
        (Ext.mk₀ ((freeModuleSheafOnOpen R (TopCat.of (PrimeSpectrum A))).map
          (homOfLE (hf i)))).comp α (zero_add (n + 1)) = 0 := by
  apply affineAbPresheaf_finiteBasicOpenVanishing
    (openSheafExtPresheaf (X := TopCat.of (PrimeSpectrum A)) F (n + 1)) U hU α
  intro x hx
  exact moduleSheafExt_locallyZero (R := R) (X := TopCat.of (PrimeSpectrum A)) F n U α x hx

end SerrePositivity.KST.DerivedGeometry

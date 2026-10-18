module

public import SerrePositivity.KST.DerivedGeometry.RingedOpenHom
public import SerrePositivity.KST.DerivedGeometry.RingedForgetExact
public import SerrePositivity.KST.DerivedGeometry.SheafExtLocalVanishing

/-!
概要：実際の環層加群層圏における自由開加群からの Ext 類の局所消滅。
方針：サイクルへの普遍的な持ち上げと基礎層での epi の局所全射性を使う。
規約：固定環への忘却が injective を保つことを仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：環層の加群層圏の Ext は Hom と同じ宇宙で存在する。
方針：Grothendieck 性から十分な injective を得て Ext の小性の定理を使う。
規約：存在を未証明のフィールドにしない。
使われ方：TT §3、Toën §3.2 の実際の係数加群層の Ext。
-/
instance ringedModule_hasExt : HasExt.{u} (SheafOfModules.{u} B) :=
  hasExt_of_enoughInjectives _

/--
概要：環層の加群層の injective 分解を構成する。
方針：Grothendieck 圏の十分な injective と標準構成を使う。
規約：元の環層上の実際の分解。
使われ方：TT §3・§8、Toën §3.2 の係数 Ext の cocycle 表示。
-/
def ringedInjectiveResolution (F : SheafOfModules.{u} B) : InjectiveResolution F :=
  InjectiveResolution.of F

/--
概要：完全な環層加群層の短複体への自由開加群からの cocycle は近傍で境界。
方針：サイクルへの射を核の普遍性で作り、境界射の基礎層の局所全射性を使う。
規約：大域切断の右完全性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Ext の局所消滅。
-/
lemma ringedExact_localHomBoundary (S : ShortComplex (SheafOfModules.{u} B)) (hS : S.Exact)
    (U : Opens X) (f : (ringedFreeSheafOnOpen X B).obj U ⟶ S.X₂) (hf : f ≫ S.g = 0)
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ g : (ringedFreeSheafOnOpen X B).obj V ⟶ S.X₁,
        g ≫ S.f = (ringedFreeSheafOnOpen X B).map (homOfLE hVU) ≫ f := by
  let c := S.liftCycles f hf
  let z := ringedFreeSheafOnOpenHomEquiv X B U S.cycles c
  let T := SheafOfModules.toSheaf.{u} B
  have : PreservesColimitsOfSize.{u, u} T := ringedToSheaf_preservesColimits X B
  have : PreservesFiniteColimits T := PreservesColimitsOfSize.preservesFiniteColimits _
  have : Epi S.toCycles := hS.epi_toCycles
  have : Epi (T.map S.toCycles) := inferInstance
  have hsur : TopCat.Presheaf.IsLocallySurjective (T.map S.toCycles).hom :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      (T.map S.toCycles)).mpr inferInstance
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (T.map S.toCycles).hom).mp hsur U z x hx
  let g := (ringedFreeSheafOnOpenHomEquiv X B V S.X₁).symm y
  have hg : g ≫ S.toCycles = (ringedFreeSheafOnOpen X B).map (homOfLE hVU) ≫ c := by
    apply (ringedFreeSheafOnOpenHomEquiv X B V S.cycles).injective
    rw [ringedFreeSheafHomEquiv_postcomp, ringedFreeSheafHomEquiv_naturality]
    change S.toCycles.val.app (.op V)
      ((ringedFreeSheafOnOpenHomEquiv X B V S.X₁) g) = _
    rw [Equiv.apply_symm_apply]
    exact hy
  refine ⟨V, hVU, hxV, g, ?_⟩
  calc
    g ≫ S.f = g ≫ S.toCycles ≫ S.iCycles := by rw [S.toCycles_i]
    _ = ((ringedFreeSheafOnOpen X B).map (homOfLE hVU) ≫ c) ≫ S.iCycles := by
      rw [← Category.assoc, hg]
    _ = (ringedFreeSheafOnOpen X B).map (homOfLE hVU) ≫ f := by
      rw [Category.assoc, S.liftCycles_i]

/--
概要：実際の環層加群層圏で自由開加群からの正次数 Ext 類は近傍で零。
方針：実際の injective 分解の cocycle を局所境界へ直し、Ext の境界判定を使う。
規約：係数の平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/
lemma ringedExt_locallyZero (F : SheafOfModules.{u} B) (n : ℕ) (U : Opens X)
    (α : Ext ((ringedFreeSheafOnOpen X B).obj U) F (n + 1)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      (Ext.mk₀ ((ringedFreeSheafOnOpen X B).map (homOfLE hVU))).comp α
        (zero_add (n + 1)) = 0 := by
  let I := ringedInjectiveResolution X B F
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n + 2) rfl
  have he := (HomologicalComplex.exactAt_iff' I.cocomplex n (n + 1) (n + 2)
    (by simp) (by simp)).mp (I.cocomplex_exactAt_succ n)
  obtain ⟨V, hVU, hxV, g, hg⟩ := ringedExact_localHomBoundary X B
    (I.cocomplex.sc' n (n + 1) (n + 2)) he U f hf x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [I.mk₀_comp_extMk]
  exact (I.extMk_eq_zero_iff _ _ _ _ n rfl).mpr ⟨g, hg⟩

end SerrePositivity.KST.DerivedGeometry

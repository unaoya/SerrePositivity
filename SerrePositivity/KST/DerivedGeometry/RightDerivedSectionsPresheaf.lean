module

public import SerrePositivity.KST.DerivedGeometry.SheafInjectiveSections

/-!
概要：右導来切断の開集合についての前層と injective 分解の自然比較。
方針：切断関手の自然な制限を右導来化し、同じ injective 分解で比較する。
規約：開ごとに独立な分解を選ばず、制限写像も比較する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の層コホモロジー前層。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：開の包含が切断関手間の制限の自然変換を与える。
方針：各層の同じ制限写像を使う。
規約：開集合の対圏の射の向きで定義する。
使われ方：TT §3、Toën §3.2 の導来制限。
-/
def sheafModuleSectionsRestriction {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    sheafModuleSections (R := R) U.unop ⟶ sheafModuleSections V.unop where
  app F := F.obj.map f
  naturality {_F _G} g := (g.hom.naturality f).symm

/--
概要：加群層の正次数の右導来切断を開集合の前層に束ねる。
方針：切断の制限の自然変換を同じ次数で右導来化する。
規約：射は右導来関手の実際の制限写像。
使われ方：TT §3、Toën §3.2 の層コホモロジー前層。
-/
def rightDerivedSectionsPresheaf
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ((sheafModuleSections U.unop).rightDerived (n + 1)).obj F
  map f := (NatTrans.rightDerived (sheafModuleSectionsRestriction f) (n + 1)).app F
  map_id U := by
    have h : sheafModuleSectionsRestriction (R := R) (𝟙 U) = 𝟙 _ := by
      apply NatTrans.ext
      funext G
      exact G.obj.map_id U
    rw [h, NatTrans.rightDerived_id]
    rfl
  map_comp f g := by
    have h : sheafModuleSectionsRestriction (R := R) (f ≫ g) =
        sheafModuleSectionsRestriction f ≫ sheafModuleSectionsRestriction g := by
      apply NatTrans.ext
      funext G
      exact G.obj.map_comp f g
    rw [h, NatTrans.rightDerived_comp]
    rfl

/--
概要：右導来切断の前層と injective 分解のコホモロジー前層は自然同型。
方針：同じ分解の右導来計算同型を使い、制限の右導来化の計算公式を適用する。
規約：対象ごとの同型だけでなく全ての制限と両立する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 比較。
-/
def rightDerivedSectionsPresheafIso
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    rightDerivedSectionsPresheaf F n ≅ injectiveSectionHomologyPresheaf F n :=
  NatIso.ofComponents (fun U => moduleSheafRightDerivedSectionsIso F U.unop n) (by
    intro U V f
    dsimp only [rightDerivedSectionsPresheaf]
    rw [InjectiveResolution.rightDerived_app_eq
      (sheafModuleSectionsRestriction f) (moduleSheafInjectiveResolution F) (n + 1)]
    simp only [moduleSheafRightDerivedSectionsIso, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl)

/--
概要：正次数の右導来切断の各コホモロジー類は局所的に零。
方針：分解による計算の自然同型を介して既証の局所消滅を移す。
規約：実際の右導来制限写像で零になる。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 比較の局所消滅。
-/
lemma rightDerivedSections_locallyZero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ)
    (U : Opens X) (z : (rightDerivedSectionsPresheaf F n).obj (.op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      (rightDerivedSectionsPresheaf F n).map (homOfLE hVU).op z = 0 := by
  let e := rightDerivedSectionsPresheafIso F n
  obtain ⟨V, hVU, hxV, hzV⟩ :=
    injectiveSectionHomology_locallyZero F n U (e.hom.app (.op U) z) x hx
  refine ⟨V, hVU, hxV, ?_⟩
  apply (ModuleCat.mono_iff_injective (e.hom.app (.op V))).mp inferInstance
  calc
    _ = (injectiveSectionHomologyPresheaf F n).map (homOfLE hVU).op
        (e.hom.app (.op U) z) :=
      congrArg (fun k => k z) (e.hom.naturality (homOfLE hVU).op)
    _ = 0 := hzV
    _ = _ := (map_zero _).symm

/--
概要：準コンパクトなアフィン開の正次数の右導来切断の類は有限基本開上で零。
方針：右導来切断の局所消滅を基本開基底と準コンパクト性で有限化する。
規約：右導来関手の実際の制限写像で各類が零になる。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン Čech 比較。
-/
lemma affineRightDerivedSections_finiteBasicOpenVanishing {A : Type u} [CommRing A]
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)) (n : ℕ)
    (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : (rightDerivedSectionsPresheaf (X := TopCat.of (PrimeSpectrum A)) F n).obj (.op U)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = U ∧ ∀ i,
        (rightDerivedSectionsPresheaf (X := TopCat.of (PrimeSpectrum A)) F n).map
          (homOfLE (hf i)).op z = 0 :=
  affinePresheaf_finiteBasicOpenVanishing
    (rightDerivedSectionsPresheaf (X := TopCat.of (PrimeSpectrum A)) F n) U hU z
    (fun x hx => rightDerivedSections_locallyZero
      (X := TopCat.of (PrimeSpectrum A)) F n U z x hx)

end SerrePositivity.KST.DerivedGeometry

module

public import SerrePositivity.KST.DerivedGeometry.ComplexAdjunctionHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
概要：完全な加法的左随伴の右随伴は非有界 K-injective 複体を保つ。
方針：acyclic な始域を完全左随伴で写し、零ホモトピーを随伴の Hom 同値で戻す。
規約：K-injective 分解の存在を未証明フィールドとして追加しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界アフィン比較の接続点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)

/--
概要：複体の随伴の Hom 同値は零鎖写像を保つ。
方針：各成分の元の Hom 同値の加法性を使う。
規約：任意の複体形状。
使われ方：TT §3、Toën §3.2 の零ホモトピーの移送。
-/
lemma adjunctionComplexHomEquiv_zero {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) (L : HomologicalComplex D c) :
    adjunctionComplexHomEquiv adj c K L 0 = 0 := by
  ext i
  exact adj.homAddEquiv_zero _ _

/--
概要：完全左随伴の右随伴への項別適用は K-injective 複体を保つ。
方針：任意の acyclic 始域からの射を移し、K-injectivity の零ホモトピーを戻す。
規約：複体の次数に下限・上限を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の非有界右導来比較。
-/
lemma rightAdjoint_map_isKInjective (adj : F ⊣ G) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : CochainComplex D ℤ) [L.IsKInjective] :
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L) where
  nonempty_homotopy_zero {K} f hK := by
    let e := adjunctionComplexHomEquiv adj (.up ℤ) K L
    let g := e.symm f
    have hFK : ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := fun n => (hK n).map F
    let h := adjunctionComplexHomotopy adj (.up ℤ)
      (CochainComplex.IsKInjective.homotopyZero g hFK)
    rw [adjunctionComplexHomEquiv_zero] at h
    have hf : adjunctionComplexHomEquiv adj (.up ℤ) K L g = f := e.apply_symm_apply f
    exact ⟨hf ▸ h⟩

end SerrePositivity.KST.DerivedGeometry

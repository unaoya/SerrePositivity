module

public import SerrePositivity.KST.DerivedGeometry.SheafSectionCycles

/-!
概要：層の短複体の切断コホモロジー前層と各類の局所消滅。
方針：サイクルの代表を選び、局所境界表示をコホモロジーへ写す。
規約：層の完全性を使い、切断関手の右完全性は仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech と層コホモロジーの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))

/--
概要：層の短複体を各開の切断の短複体へ送る前層。
方針：対象は評価、射は三つの層の同じ制限を使う。
規約：完全性は定義には要求しない。
使われ方：TT §3、Toën §3.2 の切断コホモロジー。
-/
def sectionsShortComplexPresheaf : (Opens X)ᵒᵖ ⥤ ShortComplex (ModuleCat.{u} R) where
  obj U := S.map (sheafModuleSections U.unop)
  map f :=
    { τ₁ := S.X₁.obj.map f
      τ₂ := S.X₂.obj.map f
      τ₃ := S.X₃.obj.map f
      comm₁₂ := S.f.hom.naturality f
      comm₂₃ := S.g.hom.naturality f }
  map_id U := ShortComplex.hom_ext _ _
    (S.X₁.obj.map_id U) (S.X₂.obj.map_id U) (S.X₃.obj.map_id U)
  map_comp f g := ShortComplex.hom_ext _ _
    (S.X₁.obj.map_comp f g) (S.X₂.obj.map_comp f g) (S.X₃.obj.map_comp f g)

/--
概要：層の短複体の切断のコホモロジーを開集合の前層に束ねる。
方針：切断の短複体の前層に標準のコホモロジー関手を合成する。
規約：これは切断のコホモロジーであり層自体のコホモロジー層と区別する。
使われ方：TT §3、Toën §3.2 の局所消滅の対象。
-/
def sectionHomologyPresheaf : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R :=
  sectionsShortComplexPresheaf S ⋙ ShortComplex.homologyFunctor _

/--
概要：完全な層の短複体の切断コホモロジーの任意の類は局所的に零。
方針：サイクルの代表を選び、局所境界表示とコホモロジーの自然性を使う。
規約：開を縮小する必要があることを存在文に含める。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 比較の局所消滅。
-/
lemma sectionHomologyPresheaf_locallyZero (hS : S.Exact) (U : Opens X)
    (z : (sectionHomologyPresheaf S).obj (.op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      (sectionHomologyPresheaf S).map (homOfLE hVU).op z = 0 := by
  let T := S.map (sheafModuleSections U)
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance z
  have hcycle : S.g.hom.app (.op U) (T.iCycles c) = 0 := by
    exact congrArg (fun k : T.cycles ⟶ T.X₃ => k c) T.iCycles_g
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ :=
    sheafExact_localCocycleBoundary S hS U (T.iCycles c) hcycle x hx
  let T' := S.map (sheafModuleSections V)
  let φ : T ⟶ T' := (sectionsShortComplexPresheaf S).map (homOfLE hVU).op
  have hc' : ShortComplex.cyclesMap φ c = T'.toCycles y := by
    apply (ModuleCat.mono_iff_injective T'.iCycles).mp inferInstance
    calc
      _ = φ.τ₂ (T.iCycles c) :=
        congrArg (fun k : T.cycles ⟶ T'.X₂ => k c) (ShortComplex.cyclesMap_i φ)
      _ = T'.f y := hy.symm
      _ = T'.iCycles (T'.toCycles y) :=
        (congrArg (fun k : T'.X₁ ⟶ T'.X₂ => k y) T'.toCycles_i).symm
  refine ⟨V, hVU, hxV, ?_⟩
  change ShortComplex.homologyMap φ z = 0
  rw [← hc]
  calc
    _ = T'.homologyπ (ShortComplex.cyclesMap φ c) :=
      (congrArg (fun k : T.cycles ⟶ T'.homology => k c)
        (ShortComplex.homologyπ_naturality φ))
    _ = T'.homologyπ (T'.toCycles y) := by rw [hc']
    _ = 0 := congrArg (fun k : T'.X₁ ⟶ T'.homology => k y) T'.toCycles_comp_homologyπ

end SerrePositivity.KST.DerivedGeometry

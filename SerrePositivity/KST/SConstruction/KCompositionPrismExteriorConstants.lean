module
public import SerrePositivity.KST.SConstruction.KCompositionPrismWhiskerFaces
public import SerrePositivity.KST.SConstruction.KCompositionPrismStrictFaces

/-! # 元の合成三正方形の外側二辺は元のまま定数
概要：上下面の strict な三角形の定数区間を使い、三正方形の外側二辺そのものの定数性を証明する。
方針：元の最初・最後の辺の定数 trace と strict 面の同じ trace を実合成する。
規約：正方形の辺を別の定数辺へ取り替えず、その全時刻の等式を示す。
使われ方：元の二本の適合区間と合成射の適合区間を比較する三正方形の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPrismExteriorConstantsPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 最初の正方形の元の外側辺は、全時刻で同じ頂点に固定される。 -/
lemma kKanOriginalCompositionMappingSquare_exterior_upper_constant :
    ∃ v, lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      kKanOriginalCompositionMappingSquare r F f g 0 = SSet.const v := by
  let s := kKanOriginalCompositionImage r F f g 0
  have hn : ∃ v,
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace s = SSet.const v := by
    rw [tetrahedronTrace_includeFirst, tetrahedronInitialTrace_arrow]
    obtain ⟨v, hv⟩ := kKanOriginalCompositionImage_top_trace_constant r F f g
    rw [hv]
    have hp {A B : SSet.{u}} (a : A _⦋0⦌) (b : B _⦋0⦌) :
        lift (SSet.const (X := (Δ[1] : SSet.{u})) a) (SSet.const b) =
          SSet.const (Y := A ⊗ B) (a, b) := rfl
    rw [hp, SSet.const_comp]
    exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hn
  let e := (trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 0).trans
    (kKanOriginalCompositionPrism_hom r F f g)
  have hc : ∃ w,
      (lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace s) ≫ eqToHom e = SSet.const w := by
    rw [hv, SSet.const_comp]
    exact ⟨_, rfl⟩
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare,
    kKanOriginalCompositionImage, Category.assoc, eqToHom_trans, s, e] using hc

/-- 最後の正方形の元の外側辺は、全時刻で同じ頂点に固定される。 -/
lemma kKanOriginalCompositionMappingSquare_exterior_lower_constant :
    ∃ v, lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      kKanOriginalCompositionMappingSquare r F f g 2 = SSet.const v := by
  let s := kKanOriginalCompositionImage r F f g 2
  have hn : ∃ v,
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronTrace s = SSet.const v := by
    rw [tetrahedronTrace_includeSecond, tetrahedronFinalTrace_arrow]
    obtain ⟨v, hv⟩ := kKanOriginalCompositionImage_bottom_trace_constant r F f g
    rw [hv]
    have hp {A B : SSet.{u}} (a : A _⦋0⦌) (b : B _⦋0⦌) :
        lift (SSet.const (X := (Δ[1] : SSet.{u})) a) (SSet.const b) =
          SSet.const (Y := A ⊗ B) (a, b) := rfl
    rw [hp, SSet.const_comp]
    exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hn
  let e := (trianglePrismImage_hom (kKanOriginalCompositionPrism r F f g) 2).trans
    (kKanOriginalCompositionPrism_hom r F f g)
  have hc : ∃ w,
      (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronTrace s) ≫ eqToHom e = SSet.const w := by
    rw [hv, SSet.const_comp]
    exact ⟨_, rfl⟩
  simpa only [kKanOriginalCompositionMappingSquare, trianglePrismMappingSquare,
    kKanOriginalCompositionImage, Category.assoc, eqToHom_trans, s, e] using hc

end SerrePositivity.KST.SConstruction

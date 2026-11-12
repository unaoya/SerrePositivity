module

public import SerrePositivity.KST.Spectra.SmallProductKanSequence
public import SerrePositivity.KST.Spectra.SmashSmallProductMono

/-!
概要：小積の Kan 列の構造射と各射影の厳密な可換性、および単射性。
方針：随伴射を loop の小積同型で計算し、smash と小積の単射比較へ分解する。
規約：無限・空の族も含む。構造射の単射性は各因子から証明する。
使われ方：BF 1978 §2、HA §1.4.2。Sp の任意の小積の BF 条件。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SmallProductKanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u}

/-- 小積の随伴射の座標は元の随伴射への射影。 -/
lemma adjoint_projection (X : S → KanSequence.{u}) (n : ℕ) (s : S) :
    adjoint X n ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedSmallProduct.projection (fun t ↦ ((X t).level (n + 1)).space) s) =
    PointedSmallProduct.projection (fun t ↦ ((X t).level n).space) s ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((X s).level n).space ((X s).level (n + 1)).space ((X s).sigma n) := by
  rw [← loopIso_projection, adjoint, Category.assoc, Iso.inv_hom_id_assoc,
    PointedSmallProduct.map_projection]

/-- 小積の構造射と射影は厳密に可換する。 -/
lemma sigma_projection (X : S → KanSequence.{u}) (n : ℕ) (s : S) :
    (obj X).sigma n ≫ PointedSmallProduct.projection
      (fun t ↦ ((X t).level (n + 1)).space) s =
    PointedSimplicialSet.circle.{u} ◁ PointedSmallProduct.projection
      (fun t ↦ ((X t).level n).space) s ≫ (X s).sigma n := by
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).injective
  change curry (uncurry (adjoint X n) ≫ _) = curry (_ ≫ (X s).sigma n)
  rw [curry_natural_right, curry_uncurry, curry_natural_left]
  exact adjoint_projection X n s

/-- 小積の懸垂構造射は単射な smash 比較の後に元の構造射の積を続けたもの。 -/
lemma sigma_factor (X : S → KanSequence.{u}) (n : ℕ) :
    (obj X).sigma n = PointedSmallProduct.smashComparison PointedSimplicialSet.circle.{u}
      (fun s ↦ ((X s).level n).space) ≫ PointedSmallProduct.map (fun s ↦ (X s).sigma n) := by
  apply PointedSmallProduct.hom_ext
  intro s
  rw [sigma_projection, Category.assoc, PointedSmallProduct.map_projection,
    ← Category.assoc, PointedSmallProduct.smashComparison, PointedSmallProduct.lift_projection]
  rfl

/-- 単射な点つき射の小積は単射。 -/
lemma pointedMap_mono {A B : S → PointedSimplicialSet.{u}} (f : ∀ s, A s ⟶ B s)
    [∀ s, Mono (f s).right] : Mono (PointedSmallProduct.map f).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b h
  funext s
  apply ((CategoryTheory.mono_iff_injective ((f s).right.app d)).mp inferInstance)
  exact congrFun h s

/-- 元の全ての構造射が単射なら、小積の構造射も単射。 -/
lemma sigma_mono (X : S → KanSequence.{u}) (hX : ∀ s n, Mono ((X s).sigma n).right)
    (n : ℕ) : Mono ((obj X).sigma n).right := by
  rw [sigma_factor, Under.comp_right]
  let : ∀ s, Mono ((X s).sigma n).right := fun s ↦ hX s n
  let := pointedMap_mono (fun s ↦ (X s).sigma n)
  infer_instance

end
end SerrePositivity.KST.Spectra.SmallProductKanSequence

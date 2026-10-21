module

public import SerrePositivity.InfinityCategories.Stable.PastingExtension

/-!
概要：左押し出しを含む長方形の外周を、同じ span 上の指定押し出しへ取り替える。
方針：四頂点への余錐の厳密延長を経て、五頂点の普遍余錐を付加する。
規約：五頂点の図式と外周正方形を等号で保持。使われ方：graph pullback の双対貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma pastingOuterCocone_standard_val {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    ((pastingOuterCocone F).restrict
      (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι)).val =
      spanCoconeSquareIso.hom ≫ pastingSquare F 1 := by
  change joinMap _ (𝟙 Δ[0]) ≫
    (joinMap pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ (pastingCornerCocone ≫ F)) = _
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp]
  simpa only [pastingSquare, Category.assoc] using
    congrArg (fun t => t ≫ F) pastingCornerCocone_outerSpan

lemma exists_pasting_outer_colimit_replacement {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hl : IsPushoutSquare (pastingSquare F 2))
    (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hS : IsPushoutSquare S)
    (hbase : pushoutSpan (pastingSquare F 1) = pushoutSpan S) :
    ∃ F' : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      pastingCorner.ι ≫ F' = pastingCorner.ι ≫ F ∧
        IsPushoutSquare (pastingSquare F' 0) ∧ pastingSquare F' 1 = S := by
  let p := pastingOuterBase.ι ≫ F
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  have hk : k ≫ p = pushoutSpan S := by
    change (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
      (pastingOuterBase.ι ≫ F) = _
    calc
      _ = spanSquareBoundary ≫ pastingSquare F 1 := by
        simpa only [pastingSquare, Category.assoc] using
          congrArg (fun t => t ≫ F) pastingOuterSpanIso_hom_ι
      _ = _ := hbase
  let d₀ : JoinCocone (k ≫ p) :=
    ⟨(pushoutCocone S).val, by rw [hk]; exact (pushoutCocone S).property⟩
  have hd₀ : IsColimitCone d₀ :=
    (isColimitCone_iff_of_val_eq d₀ (pushoutCocone S) rfl).2 hS
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  obtain ⟨d, hd, hdk, _⟩ :=
    exists_colimitCocone_extension_of_trivialRestriction p k d₀ hd₀
  have hleft : IsPushoutSquare (pastingCornerLeftDiagram (pastingCorner.ι ≫ F)) := by
    change IsPushoutSquare (pastingSquare F 2)
    exact hl
  obtain ⟨F', hcorner, hr, hout⟩ :=
    exists_pastingExtension_of_outerColimit (pastingCorner.ι ≫ F) hleft d hd
  refine ⟨F', hcorner, hr, ?_⟩
  apply (cancel_epi spanCoconeSquareIso.hom).1
  rw [← pastingOuterCocone_standard_val]
  change joinMap k (𝟙 Δ[0]) ≫ (pastingOuterCocone F').val = _
  rw [hout]
  exact congrArg Subtype.val hdk

end SerrePositivity.KST.LocalizingInvariants

module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexNerveUlift
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：指定辺を保つ始域の同型に沿う、局所化の普遍性の移送。
方針：全関手の前合成の同型を反転関手へ制限し、局所化の比較の同値を消去する。
規約：頂点条件だけでなく指定辺の集合の実際の像を用いる。
使われ方：宇宙を合わせた初頂点写像の局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺の像が一致する射への前合成は、反転条件を保ち反映する。 -/
lemma invertsEdges_precomp_iff_of_image {X Y E : SSet.{u}} (f : X ⟶ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : f.app (Opposite.op ⦋1⦌) '' W = V)
    (F : Y ⟶ E) : InvertsEdges (f ≫ F) W ↔ InvertsEdges F V := by
  constructor
  · intro hF s hs
    obtain ⟨t, ht, rfl⟩ := (show s ∈ f.app (Opposite.op ⦋1⦌) '' W from h.symm ▸ hs)
    exact (invertedEdges_comp_iff f F t).mp (hF ht)
  · intro hF s hs
    apply (invertedEdges_comp_iff f F s).mpr
    exact hF (h ▸ Set.mem_image_of_mem _ hs)

/-- 指定辺を保つ始域の同型への前合成は、反転関手全体の実際の同型。 -/
def invertingFunctorsPreIso {X Y : SSet.{u}} (e : X ≅ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (E : SSet.{u}) : (invertingFunctors Y E V : SSet.{u}) ≅ invertingFunctors X E W := by
  have : IsIso ((pre e.hom).app E) := by
    change IsIso ((internalHom.flip.obj E).map e.hom.op)
    infer_instance
  exact fullSubcomplexIso (asIso ((pre e.hom).app E))
    (IsInvertingFunctorVertex Y E V) (IsInvertingFunctorVertex X E W) (by
      intro v
      obtain ⟨F, rfl⟩ := (functorVertexEquiv Y E).surjective v
      unfold IsInvertingFunctorVertex
      rw [Equiv.symm_apply_apply]
      change InvertsEdges F V ↔ InvertsEdges ((functorVertexEquiv X E).symm
        ((functorVertexEquiv X E) (e.hom ≫ F))) W
      rw [Equiv.symm_apply_apply]
      exact (invertsEdges_precomp_iff_of_image e.hom W V h F).symm)

/-- 反転関手の始域同型による前合成を忘れると、周囲の全関手の前合成そのもの。 -/
lemma invertingFunctorsPreIso_hom_ι {X Y : SSet.{u}} (e : X ≅ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (E : SSet.{u}) : (invertingFunctorsPreIso e W V h E).hom ≫ (invertingFunctors X E W).ι =
      (invertingFunctors Y E V).ι ≫ (pre e.hom).app E := rfl

/-- 指定辺を保つ始域の同型を前合成した局所化から、元の局所化を回収できる。 -/
lemma isLocalization_of_precomposeIso {X Y Z : SSet.{u}} (e : X ≅ Y) (F : Y ⟶ Z)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (hG : IsLocalization (e.hom ≫ F) W) : IsLocalization F V := by
  obtain ⟨hg, hG⟩ := hG
  let hf := (invertsEdges_precomp_iff_of_image e.hom W V h F).mp hg
  refine ⟨hf, fun E _ ↦ ?_⟩
  let I := invertingFunctorsPreIso e W V h E
  have hc : localizationPrecomposition F V hf E ≫ I.hom =
      localizationPrecomposition (e.hom ≫ F) W hg E := by
    apply (cancel_mono (invertingFunctors X E W).ι).mp
    dsimp only [I]
    rw [Category.assoc, invertingFunctorsPreIso_hom_ι, ← Category.assoc,
      localizationPrecomposition_ι, localizationPrecomposition_ι,
      ← NatTrans.comp_app, ← pre_map]
  have hi : IsQCatEquivalence I.hom := (qCatEquivalenceOfIso I).isQCatEquivalence
  apply hi.cancel_right
  rw [hc]
  exact hG E

end SerrePositivity.InfinityCategories

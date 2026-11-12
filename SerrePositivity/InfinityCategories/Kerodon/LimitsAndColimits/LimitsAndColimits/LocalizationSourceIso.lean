module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexNerveUlift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-!
概要：指定辺を保つ始域の同型に沿う、局所化の普遍性の移送。
方針：全関手の前合成の同型を反転関手へ制限し、局所化の比較の同値を消去する。
規約：頂点条件だけでなく指定辺の集合の実際の像を用いる。
使われ方：宇宙を合わせた初頂点写像の局所化。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定辺の像が一致する射への前合成は、反転条件を保ち反映する。 -/
lemma invertsEdges_precomp_iff_of_image {X Y E : SSet.{u}} (f : X ⟶ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : f.app (Opposite.op ⦋1⦌) '' W = V)
    (F : Y ⟶ E) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (f ≫ F) W ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F V := by
  constructor
  · intro hF s hs
    obtain ⟨t, ht, rfl⟩ := (show s ∈ f.app (Opposite.op ⦋1⦌) '' W from h.symm ▸ hs)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertedEdges_comp_iff f F t).mp (hF ht)
  · intro hF s hs
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertedEdges_comp_iff f F s).mpr
    exact hF (h ▸ Set.mem_image_of_mem _ hs)

/-- 指定辺を保つ始域の同型への前合成は、反転関手全体の実際の同型。 -/
def invertingFunctorsPreIso {X Y : SSet.{u}} (e : X ≅ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (E : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors Y E V : SSet.{u}) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W := by
  have : IsIso ((pre e.hom).app E) := by
    change IsIso ((internalHom.flip.obj E).map e.hom.op)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (asIso ((pre e.hom).app E))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex Y E V) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E W) (by
      intro v
      obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Y E).surjective v
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex
      rw [Equiv.symm_apply_apply]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F V ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E) (e.hom ≫ F))) W
      rw [Equiv.symm_apply_apply]
      exact (invertsEdges_precomp_iff_of_image e.hom W V h F).symm)

/-- 反転関手の始域同型による前合成を忘れると、周囲の全関手の前合成そのもの。 -/
lemma invertingFunctorsPreIso_hom_ι {X Y : SSet.{u}} (e : X ≅ Y)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (E : SSet.{u}) : (invertingFunctorsPreIso e W V h E).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors Y E V).ι ≫ (pre e.hom).app E := rfl

/-- 指定辺を保つ始域の同型を前合成した局所化から、元の局所化を回収できる。 -/
lemma isLocalization_of_precomposeIso {X Y Z : SSet.{u}} (e : X ≅ Y) (F : Y ⟶ Z)
    (W : Set (X _⦋1⦌)) (V : Set (Y _⦋1⦌)) (h : e.hom.app (Opposite.op ⦋1⦌) '' W = V)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (e.hom ≫ F) W) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F V := by
  obtain ⟨hg, hG⟩ := hG
  let hf := (invertsEdges_precomp_iff_of_image e.hom W V h F).mp hg
  refine ⟨hf, fun E _ ↦ ?_⟩
  let I := invertingFunctorsPreIso e W V h E
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F V hf E ≫ I.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (e.hom ≫ F) W hg E := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι).mp
    dsimp only [I]
    rw [Category.assoc, invertingFunctorsPreIso_hom_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
      ← NatTrans.comp_app, ← pre_map]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence I.hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso I).isQCatEquivalence
  apply hi.cancel_right
  rw [hc]
  exact hG E

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

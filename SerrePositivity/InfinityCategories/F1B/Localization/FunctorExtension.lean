module
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
/-!
概要：任意の反転関手の実延長と関手同型から、全反転関手 ∞ 圏への前合成の本質的全射性を得る。
方針：反転頂点を元の実関手で表し、全包含の充満忠実性で指定同型を部分圏へ持ち上げる。
規約：延長は任意の quasicategory 標的。使われ方：局所化普遍性の本質的全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 任意反転関手の関手同型付き実延長は、全反転関手 ∞ 圏への本質的全射性を与える。 -/
lemma localizationPrecomposition_isEssentiallySurjective_of_extensions {X Q Y : SSet.{u}}
    [Quasicategory Y] (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : InvertsEdges q W)
    (h : ∀ (F : X ⟶ Y), InvertsEdges F W →
      ∃ G : Q ⟶ Y, Nonempty (FunctorIso (q ≫ G) F)) :
    IsEssentiallySurjective (localizationPrecomposition q W hq Y) := by
  intro b
  let F := (functorVertexEquiv X Y).symm b.val
  have hv : functorVertex F = b.val := (functorVertexEquiv X Y).apply_symm_apply b.val
  have hb : InvertsEdges F W := fullSubcomplexOnVertices_vertex b
  obtain ⟨G, ⟨I⟩⟩ := h F hb
  let a := (localizationPrecomposition q W hq Y).app (Opposite.op ⦋0⦌) (functorVertex G)
  have ha : (invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) a = functorVertex (q ≫ G) :=
    congrArg (fun f => f.app (Opposite.op ⦋0⦌) (functorVertex G))
      (localizationPrecomposition_ι q W hq Y)
  let J : VertexIso ((invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) a)
      ((invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) b) :=
    eqToIso (congrArg HomotopyCategory.mk ha) ≪≫ I ≪≫
      eqToIso (congrArg HomotopyCategory.mk hv)
  let ff := (isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (IsInvertingFunctorVertex X Y W)).toHoFullyFaithful
  exact ⟨functorVertex G, ⟨ff.preimageIso J⟩⟩
end SerrePositivity.InfinityCategories

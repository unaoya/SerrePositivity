module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedCounitPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomLongChainExt

/-!
概要：通常の Hom の元の圏の nerve と実際の twisted arrow の指定比較は同型である。
方針：全次数の余単位を左右の制限と中央の零次単体で比較し、単位と合わせる。
規約：比較の順射は既に両端射影の保持を検証した ordinaryHomTwistedComparison そのもの。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の指定 Yoneda の全族比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 読み戻して再び比較した単体は、元の単体と同じ各零次単体を持つ。
Kerodon Proposition 8.1.1.10（Tag 03JN）、余単位の零次への制限の法則。 -/
lemma ordinaryHomTwistedCounit_vertex (f : (TwistedArrow (nerve C)) _⦋n⦌)
    (α : ⦋0⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.map α ≫ ordinaryHomTwistedSimplex (ordinaryHomTwistedRead f) =
      edgewiseWeight.map α ≫ f := by
  have hh : ordinaryHomTwistedRead (edgewiseWeight.map α ≫ f) =
      α.toOrderHom.toFunctor ⋙ ordinaryHomTwistedRead f :=
    ComposableArrows.ext₀ (ordinaryHomTwistedRead_obj_reindex f α 0)
  rw [ordinaryHomTwistedSimplex_naturality, ← hh, ordinaryHomTwistedSimplex_read_point]

private lemma mapIndices_heq (L : ComposableArrows C (n + n + 1))
    {i j i' j' : Fin (n + n + 1 + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (L.map f) (L.map g) := by
  subst i' j'
  have hh : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 実際の twisted arrow の全単体は読み戻しと指定比較の往復で変わらない。
Kerodon Proposition 8.1.1.10（Tag 03JN）、全対象・全射を含む余単位則。 -/
lemma ordinaryHomTwistedSimplex_read (f : (TwistedArrow (nerve C)) _⦋n⦌) :
    ordinaryHomTwistedSimplex (ordinaryHomTwistedRead f) = f := by
  let g := ordinaryHomTwistedSimplex (ordinaryHomTwistedRead f)
  let L := edgewiseSimplexEquiv (nerve C) n g
  let M := edgewiseSimplexEquiv (nerve C) n f
  apply (edgewiseSimplexEquiv (nerve C) n).injective
  apply ordinaryHomLongChain_ext
  · have hh : nerveReverseChain ((joinLeftOrderHom n n).toFunctor ⋙ L) =
        nerveReverseChain ((joinLeftOrderHom n n).toFunctor ⋙ M) := by
      calc
        _ = nerveOppositeMap.app _ ((edgewiseLeft (nerve C)).app _ g) := edgewiseLongChain_left g
        _ = ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
            CategoryTheory.Prod.fst Cᵒᵖ C :=
          congrArg (fun q : nerve (OrdinaryHomElements C) ⟶ nerve Cᵒᵖ =>
            q.app (Opposite.op ⦋n⦌) (ordinaryHomTwistedRead f))
            (ordinaryHomTwistedComparison_left (C := C))
        _ = nerveOppositeMap.app _ ((edgewiseLeft (nerve C)).app _ f) :=
          ordinaryHomTwistedRead_source f
        _ = _ := (edgewiseLongChain_left f).symm
    have hh' := congrArg nerveUnreverseChain hh
    simpa only [nerveUnreverse_reverse] using hh'
  · calc
      _ = (edgewiseRight (nerve C)).app _ g := edgewiseLongChain_right g
      _ = ordinaryHomTwistedRead f ⋙ ordinaryHomElementsProjection C ⋙
          CategoryTheory.Prod.snd Cᵒᵖ C :=
        congrArg (fun q : nerve (OrdinaryHomElements C) ⟶ nerve C =>
          q.app (Opposite.op ⦋n⦌) (ordinaryHomTwistedRead f))
          (ordinaryHomTwistedComparison_right (C := C))
      _ = (edgewiseRight (nerve C)).app _ f := ordinaryHomTwistedRead_target f
      _ = _ := (edgewiseLongChain_right f).symm
  · let α : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom (OrderHom.const (Fin 1) 0)
    have hh := congrArg (edgewiseSimplexEquiv (nerve C) 0) (ordinaryHomTwistedCounit_vertex f α)
    rw [edgewiseLongChain_reindex, edgewiseLongChain_reindex] at hh
    have ha : edgewiseWeightReindexOrderHom.{u} α (0 : Fin 2) =
        (⟨n, by omega⟩ : Fin (n + n + 1 + 1)) :=
      edgewiseWeightReindexOrderHom_left.{u} α 0
    have hb : edgewiseWeightReindexOrderHom.{u} α (1 : Fin 2) =
        (⟨n + 1, by omega⟩ : Fin (n + n + 1 + 1)) :=
      edgewiseWeightReindexOrderHom_right.{u} α 0
    exact (mapIndices_heq L ha.symm hb.symm _ _).trans
      ((CategoryTheory.Functor.hcongr_hom hh (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).trans
        (mapIndices_heq M ha hb _ _))

/-- 同じ Hom の元の圏からの指定比較射は全次数で可逆である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、単位と余単位からの同型性。 -/
instance ordinaryHomTwistedComparison_isIso (C : Type u) [SmallCategory C] :
    IsIso (ordinaryHomTwistedComparison C) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  exact ⟨ordinaryHomTwistedComparison_injective n.unop.len,
    fun f => ⟨ordinaryHomTwistedRead f, ordinaryHomTwistedSimplex_read f⟩⟩

/-- 同じ両端射影を保持する、Hom の元の圏と実際の twisted arrow の指定同型。
Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の全 Hom 図式の模型比較。 -/
noncomputable def ordinaryHomTwistedIso (C : Type u) [SmallCategory C] :
    nerve (OrdinaryHomElements C) ≅ TwistedArrow (nerve C) :=
  asIso (ordinaryHomTwistedComparison C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

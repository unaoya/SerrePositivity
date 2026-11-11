module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductDKHom
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EnrichedPointPrecomposition
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableLimitCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeComparisonReflection

/-!
# 指定二包含の native な余極限性

概要：HA 3.2.4.7 の余積の普通の余錐を、実際の native な余極限へ移す。
方針：同じ Kan Hom の積比較を離散図式の全 Hom の判定へ渡す。
規約：指定した二包含と cofibrant な代表の余積を保持する。
使われ方：EInfinityTheory の coprodWith_cocone の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite MonoidalCategory
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SimplicialLocalization SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
variable (A : Type u) [CommRing A] (X Y : CAlgSimplicialCategory A)

/-- 元の二つの cofibrant な代数を標準二点の離散図式にする。 -/
def cAlgBinaryDiagram : Discrete (ULift.{u + 1} Bool) ⥤ CAlgSimplicialCategory A :=
  Discrete.functor fun j => if j.down then X else Y

/-- 元の厳密包含を Kan Hom の生成射へ送った普通の余錐。 -/
def cAlgBinaryCocone : Cocone (cAlgBinaryDiagram A X Y) where
  pt := (cofibrantAlgebraDKCoprodWith A Y).obj X
  ι := Discrete.natTrans fun j => by
    rcases j with ⟨⟨b⟩⟩
    cases b
    · exact kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInr A X Y)
    · exact kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInl A X Y)

/-- native な二脚の実際の Hom の積比較も局所化で同型。 -/
lemma cAlgActualCoprodHom_isIso (Z : CAlgSimplicialCategory A) :
    IsIso (AnodyneHomotopy.anodyneQ.map (prod.lift
      (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInl A X Y) Z)
      (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInr A X Y) Z))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have h := cAlgCoprodHomRestriction_isIso A X Y Z
  have he : Q.map (prod.lift
      (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInl A X Y) Z)
      (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInr A X Y) Z)) =
      Q.map (cAlgCoprodHomRestriction A X Y Z) := by
    apply (cancel_mono (prodComparison Q _ _)).mp
    trans prod.lift
      (Q.map (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInl A X Y) Z))
      (Q.map (kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKCoprodInr A X Y) Z))
    · exact mapPairing_prodComparison Q _ _
    · exact (congrArg₂ prod.lift (kanStrictPrecompose_localized _ _ _)
        (kanStrictPrecompose_localized _ _ _)).trans (mapPairing_prodComparison Q _ _).symm
  rw [he]
  exact h

/-- 離散添字を反転する関手の nerve は実際の同型。 -/
private def discreteOppositeNerveIso (J : Type (u + 1)) :
    nerve (Discrete J) ≅ nerve ((Discrete J)ᵒᵖ) where
  hom := nerveMap (Discrete.opposite J).inverse
  inv := nerveMap (Discrete.opposite J).functor
  hom_inv_id := by
    have h : (Discrete.opposite J).inverse ⋙ (Discrete.opposite J).functor = 𝟭 _ := by
      fapply CategoryTheory.Functor.ext
      · intro i; rfl
      · intro i j f; exact Subsingleton.elim _ _
    change nerveFunctor.map ((Discrete.opposite J).inverse.toCatHom) ≫
      nerveFunctor.map ((Discrete.opposite J).functor.toCatHom) = _
    rw [← Functor.map_comp]
    change nerveMap ((Discrete.opposite J).inverse ⋙ (Discrete.opposite J).functor) = _
    rw [h]
    rfl
  inv_hom_id := by
    have h : (Discrete.opposite J).functor ⋙ (Discrete.opposite J).inverse = 𝟭 _ := by
      fapply CategoryTheory.Functor.ext
      · intro i; rfl
      · intro i j f; exact Subsingleton.elim _ _
    change nerveFunctor.map ((Discrete.opposite J).functor.toCatHom) ≫
      nerveFunctor.map ((Discrete.opposite J).inverse.toCatHom) = _
    rw [← Functor.map_comp]
    change nerveMap ((Discrete.opposite J).functor ⋙ (Discrete.opposite J).inverse) = _
    rw [h]
    rfl

/-- 同じ普通の余錐は coherent nerve の実際の余極限である。 -/
lemma cAlgBinaryCocone_isColimit : IsColimitCone (strictNativeCocone (cAlgBinaryCocone A X Y)) := by
  let c := cAlgBinaryCocone A X Y
  let E := (Discrete.opposite (ULift.{u + 1} Bool)).inverse
  have : IsIso (nerveMap E) := (discreteOppositeNerveIso (ULift.{u + 1} Bool)).isIso_hom
  apply (strictNativeCocone_isColimit_iff c).mpr
  apply (strictCoherentCone_isLimit_iff_whisker c.op E).mpr
  let d := c.op.whisker E
  have : ∀ a b : (CAlgSimplicialCategory A)ᵒᵖ,
      SSet.KanComplex (SimplicialCategory.sHom a b) := fun a b =>
        inferInstanceAs (SSet.KanComplex (SimplicialCategory.sHom b.unop a.unop))
  apply strictCoherentCone_isLimit_of_discrete_representableComparison d
  intro z
  let H := simplicialHomDiagram (E ⋙ (cAlgBinaryDiagram A X Y).op) z
  let P : Cone H :=
    { pt := SimplicialCategory.sHom X z.unop ⨯ SimplicialCategory.sHom Y z.unop
      π := Discrete.natTrans fun j => by
        rcases j with ⟨⟨b⟩⟩
        cases b
        · exact prod.snd
        · exact prod.fst }
  let hP : IsLimit P :=
    { lift := fun s => prod.lift (s.π.app ⟨⟨true⟩⟩) (s.π.app ⟨⟨false⟩⟩)
      fac := fun s j => by rcases j with ⟨⟨b⟩⟩; cases b <;> simp [P]
      uniq := fun s m hm => by
        apply prod.hom_ext
        · have ht := hm ⟨⟨true⟩⟩
          change m ≫ (prod.fst : P.pt ⟶ SimplicialCategory.sHom X z.unop) = _ at ht
          simpa only [prod.lift_fst] using ht
        · have ht := hm ⟨⟨false⟩⟩
          change m ≫ (prod.snd : P.pt ⟶ SimplicialCategory.sHom Y z.unop) = _ at ht
          simpa only [prod.lift_snd] using ht }
  let e := hP.conePointUniqueUpToIso (limit.isLimit H)
  let a := kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
    (cofibrantAlgebraDKCoprodInl A X Y) z.unop
  let b := kanStrictPrecompose (cofibrantAlgebraRelativeCategory A)
    (cofibrantAlgebraDKCoprodInr A X Y) z.unop
  have he : limit.lift H (simplicialHomCone d z) = prod.lift a b ≫ e.hom := by
    apply limit.hom_ext
    rintro ⟨⟨k⟩⟩
    rw [limit.lift_π]
    calc
      _ = prod.lift a b ≫ P.π.app ⟨⟨k⟩⟩ := by
        cases k
        · have hf : (simplicialHomCone d z).π.app ⟨⟨false⟩⟩ = b := by
            change eHomWhiskerLeft SSet z
              (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
                (cofibrantAlgebraDKCoprodInr A X Y)).op = _
            rw [simplicialHomWhiskerLeft_op]
            rfl
          exact hf.trans (prod.lift_snd a b).symm
        · have hf : (simplicialHomCone d z).π.app ⟨⟨true⟩⟩ = a := by
            change eHomWhiskerLeft SSet z
              (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
                (cofibrantAlgebraDKCoprodInl A X Y)).op = _
            rw [simplicialHomWhiskerLeft_op]
            rfl
          exact hf.trans (prod.lift_fst a b).symm
      _ = _ := congrArg (fun t => prod.lift a b ≫ t)
        (hP.conePointUniqueUpToIso_hom_comp (limit.isLimit H) ⟨⟨k⟩⟩).symm
  have hpair := cAlgActualCoprodHom_isIso A X Y z.unop
  have hq : IsIso (AnodyneHomotopy.anodyneQ.map (representableHomotopyLimitComparison d z)) := by
    change IsIso (AnodyneHomotopy.anodyneQ.map (bousfieldKanConeComparison (simplicialHomCone d z)))
    rw [bousfieldKanConeComparison_limitLift, he, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
    (FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ hq)

end SerrePositivity.EInfinity.BarrattEccles

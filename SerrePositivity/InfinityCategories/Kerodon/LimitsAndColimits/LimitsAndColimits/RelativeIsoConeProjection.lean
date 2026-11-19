module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitRelativeIso

/-!
概要：相対同型で比較した制限錐の頂点射影。
方針：元の同じ錐の切断族の頂点を固定し、錐の空間からスライスへ同型を移す。
  文献対応：HTT 1.2.13、Kerodon §7.1（Tag 02H1）の錐の制限。
使われ方：重みを変えたときの指定切断の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

set_option backward.isDefEq.respectTransparency.types true in
private lemma slice_iso_from_family {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c d : JoinCone p)
    (i : VertexIso (X := coneFamily p) (coneFamilyVertexEquiv p c) (coneFamilyVertexEquiv p d)) :
    ∃ k : VertexIso (X := sliceOver p) c d,
      Arrow.mk ((hoFunctor.map (sliceOverProjection p)).toFunctor.map k.hom) =
        Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map i.hom) := by
  let S := sliceConeFamilyMap p
  let F := (hoFunctor.map S).toFunctor
  let ff := (isQCatEquivalence_sliceConeFamilyMap p).isFullyFaithful.toHoFullyFaithful
  let hC := congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p)))
    (sliceConeFamilyMap_app_zero p c)
  let hD := congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p)))
    (sliceConeFamilyMap_app_zero p d)
  let j : F.obj (HomotopyCategory.mk c) ≅ F.obj (HomotopyCategory.mk d) :=
    eqToIso hC ≪≫ i ≪≫ (eqToIso hD).symm
  let k : VertexIso (X := sliceOver p) c d := ff.preimageIso j
  refine ⟨k, ?_⟩
  rw [← sliceConeFamilyMap_apex, Functor.map_comp, Cat.Hom.comp_toFunctor]
  change Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map (F.map k.hom)) = _
  rw [show F.map k.hom = j.hom from ff.map_preimage j.hom]
  simp only [j, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv, Functor.map_comp,
    eqToHom_map, Category.assoc, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

/-- 底上で同型な形状写像に沿う制限は、頂点が恒等射でつながる二つの錐を与える。 -/
@[cite HTT "1.2.13" (partial := special) "底を固定した同型で制限した錐の頂点射影。"]
lemma restrictJoinCone_relativeIso_projection :
    ∀ {A B K X : SSet.{u}} [Quasicategory X]
      (p : A ⟶ K) (q : B ⟶ K) (f g : A ⟶ B)
      (hf : f ≫ q = p) (hg : g ≫ q = p)
      (h : VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg))
      (O : K ⟶ X) (d : JoinCone (q ≫ O)),
    let cF := (restrictJoinCone d f).cast (show f ≫ (q ≫ O) = p ≫ O by rw [← Category.assoc, hf])
    let cG := (restrictJoinCone d g).cast (show g ≫ (q ≫ O) = p ≫ O by rw [← Category.assoc, hg])
    ∃ i : VertexIso (X := sliceOver (p ≫ O)) cF cG,
      Arrow.mk ((hoFunctor.map (sliceOverProjection (p ≫ O))).toFunctor.map i.hom) =
        Arrow.mk (𝟙 (HomotopyCategory.mk d.vertex)) := by
  intro A B K X hX p q f g hf hg h O d cF cG
  let x := d.vertex
  let dSection := coherentConeCosliceSection d
  let π := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have hs : dSection ≫ π = q ≫ O := coherentConeCosliceSection_projection d
  let T := relativeFunctorSpace q p
  let κ := relativeFunctorSquarePost q π O dSection hs p
  let Φ := κ ≫ sectionConeFamilyMap (p ≫ O) x
  let coneOf (w : A ⟶ B) (hw : w ≫ q = p) : JoinCone (p ≫ O) :=
    (restrictJoinCone d w).cast (by rw [← Category.assoc, hw])
  have hcone (w : A ⟶ B) (hw : w ≫ q = p) :
      cosliceSectionCone (w ≫ dSection)
        (by rw [Category.assoc, hs, ← Category.assoc, hw]) = coneOf w hw := by
    apply Subtype.ext
    change sliceUnderUncurry (w ≫ dSection) = joinMap (𝟙 (Δ[0] : SSet.{u})) w ≫ d.val
    rw [sliceUnderUncurry_precomp]
    dsimp only [dSection, coherentConeCosliceSection]
    rw [sliceUnderUncurry_curry]
  have hΦ (w : A ⟶ B) (hw : w ≫ q = p) :
      Φ.app (Opposite.op ⦋0⦌) (relativeFunctorVertex q p w hw) =
        coneFamilyVertexEquiv (p ≫ O) (coneOf w hw) := by
    change (sectionConeFamilyMap (p ≫ O) x).app _
      (κ.app _ (relativeFunctorVertex q p w hw)) = _
    rw [relativeFunctorSquarePost_vertex, sectionConeFamilyMap_section_vertex, hcone w hw]
  have hΦπ : Φ ≫ coneFamilyApex (p ≫ O) = SSet.const x := by
    rw [show Φ = κ ≫ sectionConeFamilyMap (p ≫ O) x from rfl,
      Category.assoc, sectionConeFamilyMap_apex, SSet.comp_const]
  let i := (eqToIso (congrArg HomotopyCategory.mk (hΦ f hf))).symm ≪≫
    h.map Φ ≪≫ eqToIso (congrArg HomotopyCategory.mk (hΦ g hg))
  have hconst : Arrow.mk ((hoFunctor.map (SSet.const x : T ⟶ X)).toFunctor.map h.hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x)) := by
    rw [hoConstantMap_hom]
    change Arrow.mk (𝟙 (HomotopyCategory.mk (PinchedHom.constant x 0))) = _
    rw [constant_zero]
  have him : Arrow.mk ((hoFunctor.map (coneFamilyApex (p ≫ O))).toFunctor.map i.hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x)) := by
    calc
      _ = Arrow.mk ((hoFunctor.map (coneFamilyApex (p ≫ O))).toFunctor.map
          ((hoFunctor.map Φ).toFunctor.map h.hom)) := by
        simp only [i, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
          Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom,
          Arrow.arrow_mk_eqToHom_comp, VertexIso.map, Functor.mapIso_hom]
      _ = Arrow.mk ((hoFunctor.map (Φ ≫ coneFamilyApex (p ≫ O))).toFunctor.map h.hom) := by
        exact (congrArg (fun F => Arrow.mk (F.toFunctor.map h.hom))
          (hoFunctor.map_comp Φ (coneFamilyApex (p ≫ O)))).symm
      _ = _ := by rw [hΦπ]; exact hconst
  obtain ⟨j, hj⟩ := slice_iso_from_family (coneOf f hf) (coneOf g hg) i
  exact ⟨j, hj.trans him⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

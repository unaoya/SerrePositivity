module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionConeFamilyVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitRestrictionValue
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyProjectionArrow
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HoConstantMap

/-!
概要：底を固定した相対同型は、元の指定極限頂点の比較を変えない。
方針：同じ指定錐のcoslice切断を相対関手空間の全族で制限し、頂点が定値な錐の族へ送る。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存比較と制限の自然性の法則。
使われ方：R04-RI。元の復元spanと実際の底上の射の相対比較を極限頂点へ反映する。
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

/-- 同じ底上の相対同型による制限は、元の指定極限頂点比較の同じ射を返す。 -/
@[cite HTT "1.2.13" (partial := special) "既存の同値な添字による比較の、底を固定した相対同型に対する自然性。"]
lemma limitVertexIsoOfOverEquivalence_hom_eq_of_relativeIso :
∀ {A B K X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (p : A ⟶ K) (q : B ⟶ K) (f g : A ⟶ B)
    (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg))
    (ef : IsQCatEquivalence f) (eg : IsQCatEquivalence g)
    (O : K ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d),
    (limitVertexIsoOfOverEquivalence f ef hf O c d hc hd).hom =
      (limitVertexIsoOfOverEquivalence g eg hg O c d hc hd).hom := by
  intro A B K X hA hB hX p q f g hf hg h ef eg O c d hc hd
  let x := d.vertex
  let dSection := coherentConeCosliceSection d
  let π := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have hs : dSection ≫ π = q ≫ O := coherentConeCosliceSection_projection d
  let T := relativeFunctorSpace q p
  let κ := relativeFunctorSquarePost q π O dSection hs p
  let Φ := κ ≫ sectionConeFamilyMap (p ≫ O) x
  let coneOf (w : A ⟶ B) (hw : w ≫ q = p) : JoinCone (p ≫ O) :=
    (restrictJoinCone d w).cast (by rw [← Category.assoc, hw])
  have hv (w : A ⟶ B) (hw : w ≫ q = p) : (coneOf w hw).vertex = x :=
    (JoinCone.vertex_cast _ _).trans (restrictJoinCone_vertex d w)
  have hl (w : A ⟶ B) (hw : w ≫ q = p) (ew : IsQCatEquivalence w) :
      IsLimitCone (coneOf w hw) :=
    ((isLimitCone_iff_restrict_equivalentShape w ew d).mp hd).cast _
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
  have hfgArrow := (limitVertexIso_coneFamily_arrow (coneOf f hf) (coneOf g hg)
    (hl f hf ef) (hl g hg eg) i.hom).symm.trans him
  have hnorm : eqToHom (congrArg HomotopyCategory.mk (hv f hf).symm) ≫
      (limitVertexIso (coneOf f hf) (coneOf g hg) (hl f hf ef) (hl g hg eg)).hom ≫
        eqToHom (congrArg HomotopyCategory.mk (hv g hg)) = 𝟙 (HomotopyCategory.mk x) := by
    apply Arrow.mk_injective _ _
    simpa only [Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp] using hfgArrow
  have hfg : (limitVertexIso (coneOf f hf) (coneOf g hg) (hl f hf ef) (hl g hg eg)).hom ≫
      eqToHom (congrArg HomotopyCategory.mk (hv g hg)) =
        eqToHom (congrArg HomotopyCategory.mk (hv f hf)) := by
    have hh := congrArg (fun z => eqToHom (congrArg HomotopyCategory.mk (hv f hf)) ≫ z) hnorm
    simpa only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Category.comp_id] using hh
  have hvcomp (w : A ⟶ B) (hw : w ≫ q = p) (ew : IsQCatEquivalence w) :
      (limitVertexIsoOfOverEquivalence w ew hw O c d hc hd).hom =
        (limitVertexIso c (coneOf w hw) hc (hl w hw ew)).hom ≫
          eqToHom (congrArg HomotopyCategory.mk (hv w hw)) :=
    limitVertexIsoOfOverEquivalence_hom_restriction p q w hw ew O c d hc hd (hl w hw ew)
  rw [hvcomp f hf ef, hvcomp g hg eg]
  calc
    _ = (limitVertexIso c (coneOf f hf) hc (hl f hf ef)).hom ≫
        ((limitVertexIso (coneOf f hf) (coneOf g hg) (hl f hf ef) (hl g hg eg)).hom ≫
          eqToHom (congrArg HomotopyCategory.mk (hv g hg))) :=
      congrArg (fun z => (limitVertexIso c (coneOf f hf) hc (hl f hf ef)).hom ≫ z) hfg.symm
    _ = _ := by rw [← Category.assoc, limitVertexIso_hom_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeGlobalApex
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalLeftLimitComposition
public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsTransportCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitRestrictionValue

/-!
概要：元の指定した極限値の比較を、native の値の頂点移送と固定形状同型に沿う制限に分解する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma nativeValueIsoOfDiagramEq_hom_from_transport
    {A : SSet.{u}} [Quasicategory A]
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})
    {E : SSet.{u + 1}} [Quasicategory E]
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶ E}
    (hD : D = nativeLeftSectionsDiagram P O) (d : JoinCone D) (hd : IsLimitCone d) :
    let c := nativeLeftSectionsTransportCone P O hE
    let hc := nativeLeftSectionsTransportCone_isLimit P O hE
    let hv := nativeLeftSectionsTransportCone_vertex P O hE
    (nativeLeftSectionsValueIsoOfDiagramEq P O hE hD d hd).hom =
      eqToHom (congrArg HomotopyCategory.mk hv).symm ≫
        (limitVertexIsoOfDiagramEq hD.symm c d hc hd).hom := by
  subst D
  exact nativeLeftSectionsValueIso_hom_transportCone P O hE d hd
    (nativeLeftSectionsTransportCone_isLimit P O hE)

private lemma limitVertexIsoOfDiagramEq_hom_cast_source {K X : SSet.{u}} [Quasicategory X]
    {D D' : K ⟶ X} (h : D = D') (c : JoinCone D) (d : JoinCone D')
    (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (limitVertexIsoOfDiagramEq h c d hc hd).hom =
      eqToHom (congrArg HomotopyCategory.mk (JoinCone.vertex_cast c h)).symm ≫
        (limitVertexIso (c.cast h) d (hc.cast h) hd).hom := by
  subst D'
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private lemma eqToHom_two_comp {T : Type u} [Category T] {x a b c : T}
    (f : x ⟶ a) (p : a = b) (q : b = c) (r : a = c) :
    (f ≫ eqToHom p) ≫ eqToHom q = f ≫ eqToHom r := by
  subst b c
  simp only [eqToHom_refl, Category.comp_id]

private lemma eqToHom_three_comp {T : Type u} [Category T] {a b c d z : T}
    (p : a = b) (q : b = c) (r : c = d) (s : a = d) (f : d ⟶ z) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ f = eqToHom s ≫ f := by
  subst b c d
  simp only [eqToHom_refl, Category.id_comp]

/-- 元の指定した極限値の比較を、native の値の頂点移送と固定形状同型に沿う制限に分解する。
HTT 5.1.5.6（双対）、指定した右 Kan 拡張の値の比較。 -/
lemma originalLeftLimitIso_hom_nativeRestriction
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u}) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let b := nerveOppositeIso (C := C)
    let P := U.map b.hom ≫ F
    let O' := (fixedYonedaDomainIso C).inv ≫ O
    let f := U.mapIso (smallLeftUnstraighteningBaseIso b F)
    let p := U.map (smallLeftUnstraighteningProjection P) ≫ U.map b.hom
    let q := U.map (smallLeftUnstraighteningProjection F)
    let v := SSet.opObjEquiv.symm (functorVertex P)
    let t := nativeWeightedSections_valueTransport O' hE v
    let ht := nativeWeightedSections_valueTransport_isLimit O' hE v
    let hc := nativeLeftSectionsTransportCone_isLimit P O' hE
    let c := nativeLeftSectionsTransportCone P O' hE
    ∀ (hp : p ≫ O = nativeLeftSectionsDiagram P O')
      (hf : f.hom ≫ q = p) (d : JoinCone (q ≫ O)) (hd : IsLimitCone d),
    let c' := c.cast hp.symm
    (weightedSections_originalLeftLimitIso O hE F d hd).hom =
      (weightedSections_nativeLimitIso O hE (SSet.opObjEquiv.symm (functorVertex F)) t.cone ht).hom ≫
        eqToHom (congrArg HomotopyCategory.mk (t.cone_vertex.trans
          ((JoinCone.vertex_cast c hp.symm).trans (nativeLeftSectionsTransportCone_vertex P O' hE)).symm)) ≫
        (limitVertexIsoOfOverEquivalence f.hom (isPrecompositionEquivalence_of_iso f).isQCatEquivalence
          hf O c' d (hc.cast hp.symm) hd).hom := by
  intro U b P O' f p q v t ht hc c hp hf d hd c'
  let r := restrictJoinCone d f.hom
  let hr := (isLimitCone_iff_restrict_equivalentShape f.hom
    (isPrecompositionEquivalence_of_iso f).isQCatEquivalence d).mp hd
  let he : f.hom ≫ (q ≫ O) = p ≫ O := by rw [← Category.assoc, hf]
  let dr := r.cast he
  let hdr := hr.cast he
  let hv := t.cone_vertex
  let w := weightedSections_nativeLimitIso O hE (SSet.opObjEquiv.symm (functorVertex F)) t.cone ht
  let w' : VertexIso ((weightedSections O hE).app _
      (SSet.opObjEquiv.symm (functorVertex F))) (nativeLeftSectionsValue P O' hE) := by
    change VertexIso _ ((nativeWeightedSections O' hE).app _ v)
    exact hv ▸ w
  have hW : (weightedSections_leftLimitIso O hE F dr hdr).hom =
      w'.hom ≫ (nativeLeftSectionsValueIsoOfDiagramEq P O' hE hp dr hdr).hom := rfl
  have hR : (weightedSections_originalLeftLimitIso O hE F d hd).hom =
      (weightedSections_leftLimitIso O hE F dr hdr).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast r he).trans (restrictJoinCone_vertex d f.hom))) := by
    let compare : ∀ (T : (U.obj (smallLeftUnstraightening P)) ⟶ E),
        T = p ≫ O → ∀ (c₀ : JoinCone T), IsLimitCone c₀ →
          VertexIso ((weightedSections O hE).app _
            (SSet.opObjEquiv.symm (functorVertex F))) c₀.vertex := by
      intro T e₀ c₀ hc₀
      cases e₀
      exact weightedSections_leftLimitIso O hE F c₀ hc₀
    have hcomp : ∀ (T : (U.obj (smallLeftUnstraightening P)) ⟶ E)
        (e₀ : T = p ≫ O) (c₀ : JoinCone T) (hc₀ : IsLimitCone c₀),
        compare T e₀ c₀ hc₀ =
          ((JoinCone.vertex_cast c₀ e₀) ▸ (weightedSections_leftLimitIso O hE F
            (c₀.cast e₀) (hc₀.cast e₀))) := by
      intro T e₀ c₀ hc₀
      cases e₀
      rfl
    change (((restrictJoinCone_vertex d f.hom) ▸ compare _ he r hr)).hom = _
    rw [hcomp]
    have h₀ := vertexIso_transport_target_hom (restrictJoinCone_vertex d f.hom)
      ((JoinCone.vertex_cast r he) ▸ (weightedSections_leftLimitIso O hE F dr hdr))
    have h₁ := vertexIso_transport_target_hom (JoinCone.vertex_cast r he)
      (weightedSections_leftLimitIso O hE F dr hdr)
    calc
      _ = _ := h₀
      _ = _ := congrArg (fun m => m ≫ _) h₁
      _ = _ := eqToHom_two_comp _ _ _ _
  have hw : w'.hom = w.hom ≫ eqToHom (congrArg HomotopyCategory.mk hv) :=
    vertexIso_transport_target_hom hv w
  rw [hR, hW, nativeValueIsoOfDiagramEq_hom_from_transport P O' hE hp dr hdr,
    limitVertexIsoOfDiagramEq_hom_cast_source hp.symm c dr hc hdr,
    hw, limitVertexIsoOfOverEquivalence_hom_restriction p q
      f.hom hf (isPrecompositionEquivalence_of_iso f).isQCatEquivalence O c' d (hc.cast hp.symm) hd hdr]
  simp only [Category.assoc]
  exact congrArg (fun m => w.hom ≫ m) (eqToHom_three_comp _ _ _ _ _)

end SerrePositivity.InfinityCategories.Sheaves

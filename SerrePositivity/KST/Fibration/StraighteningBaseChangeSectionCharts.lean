module
public import SerrePositivity.KST.Fibration.StraighteningDiagramBaseChangeComponent
public import SerrePositivity.KST.Fibration.RelativeSectionJointVertices

/-! # 元の大域底変換を、同じ切断空間への左右の指定比較で表示する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

private lemma normalizeTriangle {C : Type v} [Category.{w} C]
    {a b s t s' t' : C} (l : a ≅ t) (e : s ≅ t) (r : b ≅ s)
    (hs : s = s') (ht : t = t') :
    l ≪≫ e.symm ≪≫ r.symm =
      F2.isoNormalizeEndpoints l rfl ht ≪≫
        (F2.isoNormalizeEndpoints e hs ht).symm ≪≫
          (F2.isoNormalizeEndpoints r rfl hs).symm := by
  subst s' t'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

private lemma mapNormalizeTriangle {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b s t : C} {s' t' : Z}
    (l : a ≅ t) (e : s ≅ t) (r : b ≅ s) (d : a ≅ b)
    (hd : d = l ≪≫ e.symm ≪≫ r.symm) (hs : F.obj s = s') (ht : F.obj t = t') :
    F.mapIso d = F2.isoNormalizeEndpoints (F.mapIso l) rfl ht ≪≫
      (F2.isoNormalizeEndpoints (F.mapIso e) hs ht).symm ≪≫
        (F2.isoNormalizeEndpoints (F.mapIso r) rfl hs).symm := by
  subst d
  rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm, Functor.mapIso_symm]
  exact normalizeTriangle _ _ _ hs ht

/-- 元の大域底変換の定義で使った、左側の切断図式への同じ比較。 -/
def straighteningJointBaseChangeLeftIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hleft) ≪≫
    (leftStraighteningSectionJointDiagram_restrictIso B).precomp t

/-- 右側も元の制限同型そのものを使う。 -/
def straighteningJointBaseChangeRightIso :=
  (leftStraighteningSectionJointDiagram_restrictIso D).postcomp
    ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})

/-- 同じ指定制限同型を、元の左右の比較と元の逆切断比較へ厳密に分解する。 -/
theorem straighteningJointBaseChangeRestrictionIso_factor :
    straighteningJointBaseChangeRestrictionIso k =
      straighteningJointBaseChangeLeftIso k ≪≫
        (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
          (straighteningJointBaseChangeRightIso k).symm := by
  simp only [straighteningJointBaseChangeRestrictionIso, straighteningJointBaseChangeLeftIso,
    straighteningJointBaseChangeRightIso, Iso.trans_assoc]

/-- 全単体の元の逆切断比較の標的は、元の底への相対切断空間。 -/
theorem transportSectionBaseChange_target_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (transportSimplexFunctor k)) ≫ transportSimplexSectionInfinity B)) =
      spaceInfinityVertex (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj X) := by
  have ht : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (transportSimplexFunctor k)) ≫ transportSimplexSectionInfinity B =
        relativeSectionDiagramInfinity (transportSimplexDomainFunctor D ⋙ Over.map k) :=
    (transportSimplexSectionInfinity_reindex (transportSimplexFunctor k)).trans
      (congrArg relativeSectionDiagramInfinity (transportSimplexDomainFunctor_baseChange k))
  have hv := congrArg functorVertex ht
  have he := congrArg ((doubleFunctorEvaluation (Y := SpaceInfinity.{u})
    (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)) hv
  exact he.trans (relativeSectionDiagramInfinity_double_vertex _ X c)

/-- 元の左比較の指定二重成分を、同じ相対切断空間への同型として表示する。 -/
def straighteningBaseChangeLeftChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (straighteningJointBaseChangeLeftIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X))) rfl
    (congrArg HomotopyCategory.mk (transportSectionBaseChange_target_vertex k X c))

/-- 元の右比較の指定二重成分を、同じ pullback 切断空間への同型として表示する。 -/
def straighteningBaseChangeRightChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (straighteningJointBaseChangeRightIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X))) rfl
    (congrArg HomotopyCategory.mk (relativeSectionDiagramInfinity_double_precomp_vertex k
      (transportSimplexDomainFunctor D) X c))

/-- 元の全単体上の切断比較も、同じ指定成分を標準切断空間で表示する。 -/
def transportSectionBaseChangeValueIso (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (transportSimplexSectionInfinity_baseChangeIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X)))
    (congrArg HomotopyCategory.mk (relativeSectionDiagramInfinity_double_precomp_vertex k
      (transportSimplexDomainFunctor D) X c))
    (congrArg HomotopyCategory.mk (transportSectionBaseChange_target_vertex k X c))

/-- 表示変更後も、元の切断比較の同じ係数成分を保持する。 -/
theorem transportSectionBaseChangeValueIso_eq (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :
    transportSectionBaseChangeValueIso k X c =
      relativeSectionBaseChangeComponentIso k (transportSimplexDomainFunctor D) X c :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (relativeSectionBaseChangeComponentIso_heq_transportMap k X c).symm

/-- 同じ元の大域制限成分は、左右の切断比較の間の同じ逆切断比較である。 -/
theorem straighteningBaseChangeSectionCharts_factor (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :
    VertexIso.map (straighteningJointBaseChangeRestrictionIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X)) =
      straighteningBaseChangeLeftChart k X c ≪≫
        (transportSectionBaseChangeValueIso k X c).symm ≪≫
          (straighteningBaseChangeRightChart k X c).symm := by
  let T := doubleFunctorEvaluation
    (K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory D)))
    (A := LeftFibrationInfinity B) (Y := SpaceInfinity.{u})
    (ULift.up (nerveVertex c)) (coherentNerveVertex X)
  exact mapNormalizeTriangle (hoFunctor.map T).toFunctor
    (straighteningJointBaseChangeLeftIso k)
    (transportSimplexSectionInfinity_baseChangeIso k)
    (straighteningJointBaseChangeRightIso k)
    (straighteningJointBaseChangeRestrictionIso k)
    (straighteningJointBaseChangeRestrictionIso_factor k)
    (congrArg HomotopyCategory.mk (relativeSectionDiagramInfinity_double_precomp_vertex k
      (transportSimplexDomainFunctor D) X c))
    (congrArg HomotopyCategory.mk (transportSectionBaseChange_target_vertex k X c))

/-- 同じ大域制限成分は、左右の元の切断比較を通じて同じ pullback 点を回収する。 -/
theorem straighteningBaseChangeSectionCharts_pointHom
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D)
    (v : ((((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).precompose
      (leftFibrationBaseChangeEnriched k)).obj c).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj X)).symm
          ((relativeFunctorBaseChangeForward X.val.hom k
            ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
              (Opposite.op ⦋0⦌) v)) ≫
      (straighteningBaseChangeLeftChart k X c).inv ≫
        (VertexIso.map (straighteningJointBaseChangeRestrictionIso k)
          (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
            (ULift.up (nerveVertex c)) (coherentNerveVertex X))).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).precompose
        (leftFibrationBaseChangeEnriched k)).obj c).obj X)).symm v) ≫
      (straighteningBaseChangeRightChart k X c).inv := by
  have hp := relativeSectionJointBaseChangeValueIso_inv_pointHom k
    (transportSimplexDomainFunctor D) X c v
  rw [relativeSectionJointBaseChangeValueIso_eq] at hp
  have hp' : cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj X)).symm
          ((relativeFunctorBaseChangeForward X.val.hom k
            ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
              (Opposite.op ⦋0⦌) v)) ≫ (transportSectionBaseChangeValueIso k X c).inv =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).precompose
        (leftFibrationBaseChangeEnriched k)).obj c).obj X)).symm v) := by
    rw [transportSectionBaseChangeValueIso_eq]
    exact hp
  rw [straighteningBaseChangeSectionCharts_factor]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have h := congrArg (fun m => m ≫ (straighteningBaseChangeRightChart k X c).inv) hp'
  exact (Category.assoc _ _ _).symm.trans h

end SerrePositivity.KST.Fibration

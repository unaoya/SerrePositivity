module
public import SerrePositivity.InfinityCategories.F2.Tensor.SetElements
public import SerrePositivity.InfinityCategories.F2.Tensor.Space
public import SerrePositivity.InfinityCategories.F1.Coherent.SmallCoherentMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits
public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalUnstraighteningStrictification
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.PullbackSections
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantRepresentableValues
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection

/-!
概要：集合値の重みとのテンソルからの写像を、元の圏の上の極限への写像に移す。
方針：空間値図式の変換を底上の写像にし、元の圏への制限と引き戻しの切断で極限を計算する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits F2.Presentable

namespace SetWeight
variable {I : Type u} [SmallCategory I] (P : I ⥤ Type u)
abbrev projection := nerveMap (Functor.Elements.π P)
abbrev diagram {E : SSet.{u + 1}} (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E) :=
  (SSet.uliftFunctor.{u + 1, u}).map (projection P) ≫ F

/-- P を始域とする変換の空間を、P.Elements 上の同じ図式の切断空間に移す。 -/
def sectionsEquivalence
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    QCatEquivalence (pinchedHom (functorVertex (spaceDiagram P)) (functorVertex G))
      ((SSet.uliftFunctor.{u + 1, u}).obj (coherentSpaceSectionsObject (diagram P G)).obj) := by
  let X := spaceDiagram P
  let p := projection P
  let q := smallLeftUnstraighteningProjection G
  let q' := smallLeftUnstraighteningProjection (diagram P G)
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).obj n) :=
    fun n => inferInstanceAs (Small.{u} (ULift.{u + 1} ((nerve I).obj n)))
  let e₀ := (small_leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence X G).choose
  let e₁ := (smallLeftUnstraighteningRelativeFunctorIso X G).symm
  let j : Over.mk p ⟶ Over.mk (smallLeftUnstraighteningProjection X) :=
    Over.homMk (elementsComparison P) (elementsComparison_projection P)
  have hj := relativeFunctorOverPre_isQCatEquivalence q j
    (elementsComparison_isPrecompositionEquivalence P)
  let bp : Over.mk q' ≅ Over.mk (pullback.snd q p) :=
    Over.isoMk (smallLeftUnstraighteningBaseChangeIso G p)
      (smallLeftUnstraighteningBaseChangeIso_hom_snd G p)
  let e₂ : relativeFunctorSpace q p ≅ simplicialSections q' :=
    (pullbackSectionsRelativeIso q p).symm ≪≫ simplicialSectionsRelativeIso _ ≪≫
      relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 _))) bp.symm ≪≫
        (simplicialSectionsRelativeIso q').symm
  exact e₀.trans ((qCatEquivalenceOfIso e₁).trans
    (hj.ulift.choose.trans (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso e₂))))

/-- 空間の頂点同型を、その Kan 複体の同値として読み戻す。 -/
def spaceValueEquivalence {x y : SpaceInfinity.{u} _⦋0⦌} (e : VertexIso x y) :
    QCatEquivalence (spaceInfinityObject x).obj (spaceInfinityObject y).obj := by
  let a := (homotopyCategory_homMk_surjective x y e.hom).choose
  have h : IsInvertibleEdge a := by
    change IsIso (Truncated.HomotopyCategory.homMk a)
    rw [(homotopyCategory_homMk_surjective x y e.hom).choose_spec]
    infer_instance
  exact (F2.Compact.spaceInfinityEdgeValue_isQCatEquivalence (SSet.Edge.ofTruncated a) h).choose

/-- 宇宙変更の図式の値を、元の空間の宇宙持ち上げと比較する。 -/
def spaceUniverseValueEquivalence (x : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject x).obj)
      (spaceInfinityObject (F2.Compact.spaceUniverseDiagram.app _ (ULift.up x))).obj := by
  let p := pointedSpaceProjection.{u}
  let G := leftStraighteningInfinityDiagram p
  have h := vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p
    (smallLeftUnstraighteningProjection G) (leftStraighteningInfinityReconstruction p)
    (leftStraighteningInfinityReconstruction_projection p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p) x
  exact (pointedSpaceFiberValueEquivalence x).symm.trans
    (h.choose.trans (smallLeftUnstraighteningFiberValueEquivalence G x))

variable {E : SSet.{u + 1}} [Quasicategory E]
variable (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 集合値前層 P で重み付けたテンソルからの写像空間。
右辺には、呼び出し側が指定した元の圏上の極限錐そのものを使う。 -/
def tensorSpaceFunctor_setWeightHom (c : JoinCone (diagram P F)) (hc : IsLimitCone c) :
    QCatEquivalence
      (pinchedHom (functorVertex (spaceDiagram P ≫ tensorSpaceFunctor hE M)) (functorVertex F))
      (pinchedHom M c.vertex) := by
  let t := spaceTensorData hE M
  let g := diagram P (F ≫ t.hom)
  have hg : IsLimitCone (mapJoinCone t.hom c) :=
    mapJoinCone_isLimit_of_adjunction t.adjunction c hc
  let e := limitVertexIso (coherentDiagramSectionsCone g) (mapJoinCone t.hom c)
    (coherentDiagramSectionsCone_isLimit g) hg
  have ev : VertexIso (coherentSpaceSectionsVertex g) (t.hom.app _ c.vertex) := by
    rw [← coherentDiagramSectionsCone_vertex g]
    exact e
  letI : KanComplex (simplicialSections (smallLeftUnstraighteningProjection g)) :=
    (coherentSpaceSectionsObject g).isKanComplex
  let vs := spaceValueEquivalence ev
  let hs := (qCatEquivalenceOfIso (eqToIso (coherentSpaceSectionsVertex_object g))).symm.trans vs
  exact (tensorSpaceFunctor_diagramHom hE M (spaceDiagram P) F).trans
    ((sectionsEquivalence P (F ≫ t.hom)).trans (hs.isQCatEquivalence.ulift.choose.trans
      ((spaceUniverseValueEquivalence (t.hom.app _ c.vertex)).trans
        ((spaceValueEquivalence (t.represents.app (ULift.up c.vertex))).symm.trans
          (covariantRepresentableValueEquivalence M c.vertex)))))

/- C3: compatibility declarations; use the specified Natural comparison. -/
attribute [deprecated "Use `SerrePositivity.InfinityCategories.SetWeight.sectionsEquivalenceNatural` from `SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality`." (since := "2026-11-05")]
  sectionsEquivalence
attribute [deprecated "Use `SerrePositivity.InfinityCategories.SetWeight.tensorSpaceFunctor_setWeightHomNatural` from `SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality`." (since := "2026-11-05")]
  tensorSpaceFunctor_setWeightHom

end SetWeight
end SerrePositivity.InfinityCategories

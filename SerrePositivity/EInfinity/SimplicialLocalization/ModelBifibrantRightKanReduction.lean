module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape
public import SerrePositivity.EInfinity.FrameHom.FrameAugmentationLimitLegs
public import SerrePositivity.EInfinity.FrameHom.FrameRightKanCanonical
public import SerrePositivity.EInfinity.FrameHom.HomotopyComponentTransport
public import SerrePositivity.InfinityCategories.Derived.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Derived.ConeLegRestriction
public import SerrePositivity.InfinityCategories.Derived.RightKanTransportComponents
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightCanonicalMapping
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightConstantFamily
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightPrecompositionFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.RightKanCriterion

/-!
概要：同じ bifibrant frame の余終性を三つの実 right Kan 判定入力に還元する。
方針：代数版の元の極限・標準錐・指定単位の証明を一般モデル圏へ移す。
規約：余終性は未証明の明示入力として残し、局所化普遍性の完成と扱わない。
使われ方：一般モデルの frame→hammock 比較から局所化普遍性への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (q : ∀ X : BifibrantObject C, CofibrantResolution (C := C) simplex X.obj)
  (hcofinal : ∀ X, IsLeftCofinal (modelBifibrantFrameRightKanMap X (q X)))


include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
def modelBifibrantHammockObject
    (z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌) : BifibrantObject C :=
  AsSmall.down.obj (coherentNerveObject
    (C := KanHammockCategory (modelBifibrantRelativeCategory C)) z)

/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantHammockVertex_object
    (z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌) :
    modelBifibrantHammockVertex (modelBifibrantHammockObject z) = z :=
  (hammockLocalizationNerveMap_vertex (modelBifibrantRelativeCategory C)
    (modelBifibrantObject C (modelBifibrantHammockObject z))).trans
      (coherentNerveVertex_object
        (C := KanHammockCategory (modelBifibrantRelativeCategory C)) z)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanDiagram_hasLimit (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C))) :
    HasLimit (rightKanDiagram (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F (modelBifibrantHammockVertex X)) := by
  apply hasLimit_of_leftCofinal (modelBifibrantFrameRightKanMap X (q X))
    (hcofinal X)
  exact (congrArg HasLimit (modelBifibrantFrameRightKanMap_diagram X (q X) F)).mpr
    (modelBifibrantFrame_hasLimit X (q X) F hF)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌) :
    HasLimit (rightKanDiagram (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F z) :=
  (congrArg (fun t => HasLimit (rightKanDiagram
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) F t))
      (modelBifibrantHammockVertex_object z)).mp
    (modelBifibrantSourceRightKanDiagram_hasLimit q hcofinal (modelBifibrantHammockObject z) F hF)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantInvertingFunctor_rightKanExtension_exists
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C))) :
    ∃ (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
      (α : SSet.Homotopy
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) F),
        IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
          F G α :=
  F1B.exists_kanRightExtension_of_local_limits
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) F
    (modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality q hcofinal F hF)



include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanCanonicalCone_isLimit (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E) :
    IsLimitCone (rightKanCanonicalCone
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) G
      (modelBifibrantHammockVertex X)) :=
  FrameHom.FrameArrows.frameRightKanCanonicalCone_isLimit (modelBifibrantDKFrame X (q X))
    (modelBifibrantDKFrameAugmentation X (q X))
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
    (modelBifibrantFrameAugmentation_invertible X (q X))
    (hcofinal X) modelFrameIndex_weaklyContractible G

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanCanonicalCone_isLimit_all
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
    (z : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌) :
    IsLimitCone (rightKanCanonicalCone
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) G z) :=
  (congrArg (fun t => IsLimitCone (rightKanCanonicalCone
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) G t))
      (modelBifibrantHammockVertex_object z)).mp
    (modelBifibrantSourceRightKanCanonicalCone_isLimit q hcofinal (modelBifibrantHammockObject z) G)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanExtension_refl_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E) :
    IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) G
      (functorHomotopyRefl
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G)) :=
  F1B.kanRightKanExtension_refl_of_canonicalLimits
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) G
    (modelBifibrantSourceRightKanCanonicalCone_isLimit_all q hcofinal G)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantHammockLocalizationPrecomposition_isFullyFaithful
    (E : SSet.{max u v}) [Quasicategory E] :
    IsFullyFaithful (localizationPrecomposition
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (weakNerveEdges (modelBifibrantRelativeCategory C))
      (hammockLocalizationNerveMap_inverts (modelBifibrantRelativeCategory C)) E) :=
  localizationPrecomposition_isFullyFaithful_of_rightKan _ _ _
    (fun _ _ => modelBifibrantSourceRightKanExtension_refl_of_frameCofinality q hcofinal) E


section Legs
variable (X : BifibrantObject C)

include q in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceFrameAugmentation_image_invertible
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (n : AsSmall.{max u v} SimplexCategory) :
    IsInvertibleEdge ((nerve.edgeMk
      ((modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated := by
  have hw := hF (show ComposableArrows.mk₁ ((modelBifibrantDKFrameAugmentation X (q X)).app n) ∈
      weakNerveEdges (modelBifibrantRelativeCategory C) from
    ⟨_, _, _, modelBifibrantDKFrameAugmentation_weak X (q X) n, rfl⟩)
  change IsInvertibleEdge
    ((edgeOfSimplex (ComposableArrows.mk₁ ((modelBifibrantDKFrameAugmentation X (q X)).app n))).map
      ((truncation 2).map F)) at hw
  exact (isInvertibleEdge_congr (e :=
    (edgeOfSimplex (ComposableArrows.mk₁ ((modelBifibrantDKFrameAugmentation X (q X)).app n))).map
      ((truncation 2).map F))
    (f := ((nerve.edgeMk ((modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated)
    rfl).mp hw

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanLimitCone_leg_isInvertible
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (c : JoinCone (rightKanDiagram
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) F
      (modelBifibrantHammockVertex X))) (hc : IsLimitCone c)
    (i : (nerve (AsSmall.{max u v} SimplexCategory)) _⦋0⦌) :
    IsInvertibleEdge (F2.nativeConeLeg c
      ((modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) i)) := by
  let u := modelBifibrantFrameRightKanMap X (q X)
  have hu := hcofinal X
  have he := modelBifibrantFrameRightKanMap_diagram X (q X) F
  let d : JoinCone (nerveMap (modelBifibrantDKFrame X (q X)) ≫ F) :=
    ⟨(restrictJoinCone c u).val, (restrictJoinCone c u).property.trans he⟩
  have hd : IsLimitCone d := (F1B.kanIsLimitCone_congr he (restrictJoinCone c u) d rfl).mp
    ((isLimitCone_iff_restrict_of_leftCofinal u hu _ c).mp hc)
  have h := FrameHom.FrameArrows.augmentationLimitCone_leg_isInvertible
    (modelBifibrantDKFrame X (q X)) (modelBifibrantDKFrameAugmentation X (q X)) F
    (modelBifibrantSourceFrameAugmentation_image_invertible q X F hF)
    modelFrameIndex_weaklyContractible d hd i
  have he' : (F2.nativeConeLeg d i).edge =
      (F2.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge :=
    nativeConeLeg_restrict_edge c u i
  exact (isInvertibleEdge_congr he').mp h

end Legs


include q in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceFrameRightKanMap_frame_projection (X : BifibrantObject C)
    (n : AsSmall.{max u v} SimplexCategory) :
    (rightKanProjection (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X)).app (Opposite.op ⦋0⦌)
      ((modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) (nerveVertex n)) =
    nerveVertex ((modelBifibrantDKFrame X (q X)).obj n) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (modelBifibrantFrameRightKanMap_projection X (q X)) (Opposite.op ⦋0⦌)) (nerveVertex n)
  rw [NatTrans.comp_app_apply] at h
  exact h.trans (ComposableArrows.ext₀ rfl)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_frame_isInvertible (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F G α) (n : AsSmall.{max u v} SimplexCategory) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge α
      (nerveVertex ((modelBifibrantDKFrame X (q X)).obj n))).toTruncated := by
  obtain ⟨t, ht⟩ := hα (modelBifibrantHammockVertex X)
  let i := nerveVertex n
  let v := (modelBifibrantFrameRightKanMap X (q X)).app (Opposite.op ⦋0⦌) i
  have hqG := (hammockLocalizationNerveMap_inverts (modelBifibrantRelativeCategory C)).comp G
  have h₀ := modelBifibrantSourceRightKanLimitCone_leg_isInvertible q hcofinal X _ hqG
    (rightKanCanonicalCone (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      G (modelBifibrantHammockVertex X))
    (modelBifibrantSourceRightKanCanonicalCone_isLimit q hcofinal X G) i
  have h₁ := modelBifibrantSourceRightKanLimitCone_leg_isInvertible q hcofinal X F hF t.cone ht i
  have hi := t.component_isInvertible_of_legs v h₀ h₁
  exact (congrArg (fun z => IsInvertibleEdge
    (simplicialHomotopyVertexEdge α z).toTruncated)
      (modelBifibrantSourceFrameRightKanMap_frame_projection q X n)).mp hi

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_vertex_isInvertible (X : BifibrantObject C)
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F G α) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge α
      (nerveVertex (modelBifibrantObject C X))).toTruncated := by
  let n : AsSmall.{max u v} SimplexCategory := ⟨⦋0⦌⟩
  let e := (nerve.edgeMk ((modelBifibrantDKFrameAugmentation X (q X)).app n)).toTruncated
  apply FrameHom.homotopyComponent_target_isInvertible α e
    (modelBifibrantSourceRightKanUnit_frame_isInvertible q hcofinal X F hF G α hα n)
  · exact (isInvertibleEdge_congr (e := e.map ((truncation 2).map
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G)))
      (f := ((nerve.edgeMk ((modelBifibrantDKFrameAugmentation X (q X)).app n)).map
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G)).toTruncated)
      rfl).mpr (modelBifibrantSourceFrameAugmentation_image_invertible q X _
        ((hammockLocalizationNerveMap_inverts (modelBifibrantRelativeCategory C)).comp G) n)
  · exact (isInvertibleEdge_congr (e := e.map ((truncation 2).map F))
      (f := ((nerve.edgeMk ((modelBifibrantDKFrameAugmentation X (q X)).app n)).map F).toTruncated)
      rfl).mpr (modelBifibrantSourceFrameAugmentation_image_invertible q X F hF n)

include q hcofinal in
/-- 概要：同じ bifibrant frame の余終性から元の right Kan データを回収する。
方針：元の frame・全錐・全単位を保持して一般判定へ渡す。
規約：余終性は明示入力。使われ方：一般モデルの局所化普遍性の還元。 -/
lemma modelBifibrantSourceRightKanUnit_isInvertible_of_frameCofinality
    {E : SSet.{max u v}} [Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C)))
    (G : kanHammockNerve (modelBifibrantRelativeCategory C) ⟶ E)
    (α : SSet.Homotopy
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C) ≫ G) F)
    (hα : IsRightKanExtension (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      F G α) (z : (nerve (modelBifibrantRelativeCategory C).category) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge α z).toTruncated := by
  let X : BifibrantObject C := AsSmall.down.obj (z.obj 0)
  have hz : nerveVertex (modelBifibrantObject C X) = z :=
    ComposableArrows.ext₀ rfl
  exact (congrArg (fun t => IsInvertibleEdge (simplicialHomotopyVertexEdge α t).toTruncated)
    hz).mp (modelBifibrantSourceRightKanUnit_vertex_isInvertible q hcofinal X F hF G α hα)


include q hcofinal in
/-- 概要：同じ frame の余終性から bifibrant hammock の局所化普遍性を得る。
方針：三つの実 right Kan 入力を既存の判定に代入する。
規約：余終性は明示入力で残る。使われ方：その証明後の一般モデル局所化。
-/
lemma modelBifibrantHammock_isLocalization_of_frameCofinality :
    IsLocalization (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (weakNerveEdges (modelBifibrantRelativeCategory C)) := by
  apply isLocalization_of_rightKan_local_limits
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
    (weakNerveEdges (modelBifibrantRelativeCategory C))
    (hammockLocalizationNerveMap_inverts (modelBifibrantRelativeCategory C))
  · intro E _ G
    exact modelBifibrantSourceRightKanExtension_refl_of_frameCofinality q hcofinal G
  · intro E _ F hF z
    exact modelBifibrantSourceRightKanDiagram_hasLimit_all_of_frameCofinality q hcofinal F hF z
  · intro E _ F hF G α hα x
    exact modelBifibrantSourceRightKanUnit_isInvertible_of_frameCofinality q hcofinal F hF G α hα x

end SerrePositivity.EInfinity.SimplicialLocalization

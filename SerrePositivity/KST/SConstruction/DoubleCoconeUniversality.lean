module
public import SerrePositivity.KST.SConstruction.RelativeUniversalityComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits

/-! # 二方向の余錐補完の普遍性
概要：二つの余錐方向をどちらから補完しても、固定された二重図式上の相対始対象を得る。
方針：相対境界充填の合成と内部 Hom の前合成の可換性を使う。
規約：各段の普遍性を明示する。使われ方：cofiber の二方向の交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 Hom による前合成射の族も inner fibration。
方針：二重内部 Hom を交換し、一つの前合成の inner fibration へ移す。
規約：i は単射、標的は quasicategory。使われ方：二重余錐の固定 fiber。 -/
instance ihom_pre_innerFibration {A B K C : SSet.{u}} [Quasicategory C]
    (i : A ⟶ B) [Mono i] : InnerFibration ((ihom K).map ((pre i).app C)) := by
  have he : (ihom K).map ((pre i).app C) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K B C).hom ≫ (pre i).app ((ihom K).obj C) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K A C).inv := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K A C).hom).1
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre i
  constructor
  rw [he]
  apply innerFibrations.comp_mem
  · exact MorphismProperty.of_isIso innerFibrations _
  · apply innerFibrations.comp_mem
    · exact mem_innerFibrations _
    · exact MorphismProperty.of_isIso innerFibrations _

/-- 概要：二つの余錐を元の二変数の図式に制限する射。
方針：外側の添字を制限し、内側の余錐も図式へ制限する。
規約：二重内部 Hom の源を固定する。使われ方：二方向の補完の共通の基底。 -/
def doubleCoconeRestriction (J K C : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj C) ⟶
      (ihom J).obj ((ihom K).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj C) ≫
    (ihom J).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C)

/-- 概要：二方向の図式への制限は inner fibration。
方針：二つの制限射の inner fibration 性を合成する。
規約：J・K は任意。使われ方：固定された二重図式上の補完の比較。 -/
instance doubleCoconeRestriction_innerFibration (J K C : SSet.{u}) [Quasicategory C] :
    InnerFibration (doubleCoconeRestriction J K C) := by
  have hi : InnerFibration ((ihom J).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction
    infer_instance
  exact ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations _) (mem_innerFibrations _)⟩

/-- 概要：二方向の制限の順序は厳密に交換できる。
方針：外側前合成の自然性を内側前合成に適用する。
規約：源と終域は同じ二重内部 Hom。使われ方：補完順序の比較。 -/
lemma doubleCoconeRestriction_otherOrder (J K C : SSet.{u}) :
    doubleCoconeRestriction J K C =
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J ((ihom K).obj C) := by
  exact ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}))).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C)).symm

/-- 概要：外側を普遍補完し、内側の各境界も普遍なら二重補完は相対始対象。
方針：外側余極限の相対普遍性と内側の点ごとの相対普遍性を合成する。
規約：二段階の前提を区別する。使われ方：余極限の交換の第一の順序。 -/
lemma doubleCocone_initial_outer_inner {J K C : SSet.{u}} [Quasicategory C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj C)
    (houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (⟨F, rfl⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F)))
    (hinner : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F).app (Opposite.op ⦋0⦌) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (doubleCoconeRestriction J K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  exact InitialBoundaryLifting.comp _ _ houter.initialBoundaryLifting
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_ihom_of_pointwise (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F) hinner)

/-- 概要：内側を全点で普遍補完し、制限後の外側も普遍なら二重補完は相対始対象。
方針：内側の点ごとの相対普遍性と外側余極限の相対普遍性を逆順に合成する。
規約：外側の錐頂点でも内側の普遍性を仮定する。
使われ方：余極限の交換の第二の順序。 -/
lemma doubleCocone_initial_inner_outer {J K C : SSet.{u}} [Quasicategory C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj C)
    (hinner : ∀ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C) (F.app (Opposite.op ⦋0⦌) j))
    (houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (⟨F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C, rfl⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ≫ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (doubleCoconeRestriction J K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  rw [doubleCoconeRestriction_otherOrder]
  exact InitialBoundaryLifting.comp _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_ihom_of_pointwise (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K C) F hinner)
    houter.initialBoundaryLifting

/-- 概要：同じ二重図式の上の二つの普遍補完は関手として同型。
方針：共通の制限射の fiber の始対象の一意性を使う。
規約：全二重余錐の coherent な同型。使われ方：二方向の cofiber 補完の比較。 -/
def doubleCoconeUniversalIso {J K C : SSet.{u}} [Quasicategory C]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj C)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (doubleCoconeRestriction J K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (doubleCoconeRestriction J K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (he : (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) =
      (doubleCoconeRestriction J K C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  relativeInitialVertexIso (doubleCoconeRestriction J K C) hF hG he

end SerrePositivity.KST.SConstruction

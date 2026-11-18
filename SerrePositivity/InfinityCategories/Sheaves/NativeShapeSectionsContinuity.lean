module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Sheaves.NativeRightKanContinuity
public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsData
public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoData

/-!
概要：指定形状に移した実反対 Yoneda の同じ右 Kan 延長は小余極限を極限へ送る。
方針：HTT 5.1.5.6 の反転版を、実際の形状同型と指定余単位の法則で移す。
規約：元の固定反対 Yoneda への関手同型移送は別の接続とする。
使われ方：一般重みの切断の余極限比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 実 Yoneda の指定形状版に沿う一つの全関手は、指定右 Kan 条件と余極限の反転を併せ持つ。
HTT 5.1.5.6 の双対の特殊化（小さい通常の site、presentable 係数）。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site と presentable 係数で、反対 Yoneda の指定形状版への右 Kan 延長と全小余極限の反転に特殊化する。圏同値全体は含めない。"]
lemma exists_nativeShapeSections_continuous (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (H : (PresheafCat C SpaceInfinity.{u}).op ⟶ E)
      (ε : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ H) O),
      IsRightKanExtension (nativeSetShapeOppositeYoneda C) O H ε ∧
      ∀ {I : SSet.{u}} {p : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ PresheafCat C SpaceInfinity.{u}}
        (c : JoinCocone p), IsColimitCone c →
          IsLimitCone (mapJoinCone H (coconeReverseCone c)) := by
  let a := fixedYonedaDomainIso C
  let Q := fixedPresheafShapeIso C
  let b := (SSet.opFunctor.mapIso Q).symm
  let O' := a.inv ≫ O
  let G := nativeWeightedSections O' hE
  let α := (nativeWeightedSectionsData O' hE).2.val
  have hα := nativeWeightedSections_isRightKanExtension O' hE
  have hr := kanRightKanExtension_of_isoSquare a b (nativeSetShapeOppositeYoneda_square C) α hα
  have he : a.hom ≫ O' = O := by
    dsimp only [O']
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hx : ∃ ε, IsRightKanExtension (nativeSetShapeOppositeYoneda C) (a.hom ≫ O')
      (b.hom ≫ G) ε := ⟨_, hr⟩
  rw [he] at hx
  obtain ⟨ε, hε⟩ := hx
  refine ⟨b.hom ≫ G, ε, hε, ?_⟩
  intro I p c hc
  have hc' : IsColimitCone (mapJoinCocone Q.inv c) :=
    (isColimitCone_iff_mapJoinCocone_of_trivialKanFibration Q.inv c).mp hc
  have hh := nativeRightKan_map_colimit_isLimit α hα (mapJoinCocone Q.inv c) hc'
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hh
  change (coconeReverseCone (mapJoinCocone Q.inv c)).val ≫ G =
    (coconeReverseCone c).val ≫ (b.hom ≫ G)
  rw [coconeReverseCone_val, coconeReverseCone_val]
  change (_ ≫ _ ≫ SSet.opFunctor.map (c.val ≫ Q.inv)) ≫ G =
    (_ ≫ _ ≫ SSet.opFunctor.map c.val) ≫ (SSet.opFunctor.map Q.inv ≫ G)
  rw [Functor.map_comp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Sheaves

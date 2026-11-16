module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsLocalComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoLimitVertex

/-!
概要：固定した元の全切断関手の値と、実際の反対 Yoneda の指定局所極限を比較する。
方針：元の全族の比較と前層形状の指定同型を、指定極限の頂点比較で合成する。
規約：元の切断関手を変えず、係数と重みを指定した同型で移す。
使われ方：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の離散重みへの接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ元の全切断関手の値を、実際の Yoneda の指定局所極限の頂点へ移す。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、形状・係数の指定同型の合成則。 -/
def weightedSections_nativeLimitIso (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
    (d : JoinCone (rightKanDiagram (SSet.opFunctor.map (yonedaInfinityMap (nerve C)))
      ((fixedYonedaDomainIso C).inv ≫ O)
      ((SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv.app (Opposite.op ⦋0⦌) P)))
    (hd : IsLimitCone d) : VertexIso ((weightedSections O hE).app _ P) d.vertex := by
  let a := fixedYonedaDomainIso C
  let b := (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).symm
  let O' := a.inv ≫ O
  have he : a.hom ≫ O' = O := by
    dsimp only [O']
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let c := Classical.choose (weightedSections_limitValue O hE P)
  have hc := (Classical.choose_spec (weightedSections_limitValue O hE P)).1
  have hlocal : HasLimit (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P) :=
    (hasLimit_fixedYonedaDiagram_iff_nativeShape C O P).mp ⟨c, hc⟩
  have hs : HasLimit (rightKanDiagram (nativeSetShapeOppositeYoneda C) (a.hom ≫ O') P) := by
    rw [he]
    exact hlocal
  let s := Classical.choose hs
  have hs' := Classical.choose_spec hs
  have htransport : ∀ (O₀ : Presheaf C E) (h : O₀ = O)
      (t : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O₀ P)),
      IsLimitCone t → VertexIso ((weightedSections O hE).app _ P) t.vertex := by
    intro O₀ h t ht
    cases h
    exact weightedSections_nativeShapeLimitIso O hE P t ht
  let es := htransport (a.hom ≫ O') he s hs'
  let ed := rightKanLimitVertexIsoOfIsoSquare a b
    (nativeSetShapeOppositeYoneda_square C) O' P s d hs' hd
  exact es ≪≫ ed

end SerrePositivity.InfinityCategories.Sheaves

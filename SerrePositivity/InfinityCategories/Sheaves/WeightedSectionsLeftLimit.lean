module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeLimitComparison
public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeValue

/-!
概要：元の全重み切断の値を、移した重みの小さい left 全空間の指定極限へ接続する。
方針：指定形状同型と native な指定極限の比較を合成し、係数の逆同型を消去する。
  文献対応：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）、S8 の離散重みへの接続。
規約：元の全切断関手、重み、指定した極限錐を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の全切断関手の値を、同じ重みの小さい left 全空間の指定極限へ移す。
HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）、指定した形状・係数移送の合成則。 -/
def weightedSections_leftLimitIso (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O))
    (hd : IsLimitCone d) :
    VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F))) d.vertex := by
  let P := (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F
  let O' := (fixedYonedaDomainIso C).inv ≫ O
  let v := SSet.opObjEquiv.symm (functorVertex P)
  let c := Classical.choose (nativeWeightedSections_limitValue O' hE v)
  have hc := Classical.choose_spec (nativeWeightedSections_limitValue O' hE v)
  let ew : VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F)))
      c.vertex := by
    exact weightedSections_nativeLimitIso O hE (SSet.opObjEquiv.symm (functorVertex F)) c hc.1
  have he : (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
        (uliftOppositeIso (nerve C)).hom ≫ O' := by
    dsimp only [O', fixedYonedaDomainIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have htransport : ∀ (D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶ E),
      D = (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
        (uliftOppositeIso (nerve C)).hom ≫ O' →
      ∀ t : JoinCone D, IsLimitCone t →
        VertexIso ((nativeWeightedSections O' hE).app _ v) t.vertex := by
    intro D h t ht
    cases h
    exact nativeWeightedSections_leftLimitIso P O' hE t ht
  let en := htransport _ he d hd
  have ew' : VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F)))
      ((nativeWeightedSections O' hE).app _ v) := hc.2 ▸ ew
  exact ew' ≪≫ en

end SerrePositivity.InfinityCategories.Sheaves

module

public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsComparisonLaws

/-!
概要：元の left 全空間の同じ値比較を、係数図式の等式に沿って移す法則。
方針：等式の帰納法で型を揃え、元の指定極限比較の合成則を使う。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存比較の係数移送。選択は変えない。
使われ方：S8 の元の全切断の値比較にある局所的な係数の書き換えを扱う。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A]
  (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})
  {E : SSet.{u + 1}} [Quasicategory E]
  (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
  (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)

/-- 係数の等式で型だけを移した同じ値比較。 -/
def nativeLeftSectionsValueIsoOfDiagramEq
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶ E}
    (hD : D = nativeLeftSectionsDiagram P O) (d : JoinCone D) (hd : IsLimitCone d) :
    VertexIso (nativeLeftSectionsValue P O hE) d.vertex := by
  cases hD
  exact nativeLeftSectionsValueIso P O hE d hd

/-- 係数等式による移送は、同じ標準極限比較との合成に両立する。 -/
lemma nativeLeftSectionsValueIsoOfDiagramEq_comp
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶ E}
    (hD : D = nativeLeftSectionsDiagram P O) (d e : JoinCone D)
    (hd : IsLimitCone d) (he : IsLimitCone e) :
    nativeLeftSectionsValueIsoOfDiagramEq P O hE hD d hd ≪≫ limitVertexIso d e hd he =
      nativeLeftSectionsValueIsoOfDiagramEq P O hE hD e he := by
  cases hD
  exact nativeLeftSectionsValueIso_comp P O hE d e hd he

/-- 同じ係数移送の合成則を順射で読む。 -/
lemma nativeLeftSectionsValueIsoOfDiagramEq_hom_comp
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶ E}
    (hD : D = nativeLeftSectionsDiagram P O) (d e : JoinCone D)
    (hd : IsLimitCone d) (he : IsLimitCone e) :
    (nativeLeftSectionsValueIsoOfDiagramEq P O hE hD d hd).hom ≫
      (limitVertexIso d e hd he).hom =
        (nativeLeftSectionsValueIsoOfDiagramEq P O hE hD e he).hom := by
  have h := congrArg (fun q : VertexIso (nativeLeftSectionsValue P O hE) e.vertex => q.hom)
    (nativeLeftSectionsValueIsoOfDiagramEq_comp P O hE hD d e hd he)
  exact h

end SerrePositivity.InfinityCategories.Sheaves

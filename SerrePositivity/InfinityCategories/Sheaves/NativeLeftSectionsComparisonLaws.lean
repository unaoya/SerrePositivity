module

public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiagramEqLimitVertexComposition

/-!
概要：同じ指定余単位からの left 全空間の値比較を、型を固定した補助定義で計算する。
方針：図式と頂点の型を先に固定し、元の比較そのものに標準極限比較の合成則を適用する。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存比較の法則。選択は変えない。
使われ方：S8 の元の離散重みの値の比較の照合。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A]
  (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})
  {E : SSet.{u + 1}} [Quasicategory E]
  (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)

/-- 元の同じ left 射影と係数の図式に名前を付け、型の展開を局所化する。 -/
def nativeLeftSectionsDiagram : (SSet.uliftFunctor.{u + 1, u}).obj
    (smallLeftUnstraightening P) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
    (uliftOppositeIso A).hom ≫ O

/-- 元の同じ全切断関手の同じ頂点。 -/
def nativeLeftSectionsValue
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    E _⦋0⦌ :=
  (nativeWeightedSections (A := A) O hE).app _ (SSet.opObjEquiv.symm (functorVertex P))

/-- 元の値比較そのものの型を固定した表示。新しい比較は選ばない。 -/
def nativeLeftSectionsValueIso
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (d : JoinCone (nativeLeftSectionsDiagram P O)) (hd : IsLimitCone d) :
    VertexIso (nativeLeftSectionsValue P O hE) d.vertex :=
  nativeWeightedSections_leftLimitIso (A := A) (E := E) P O hE d hd

/-- 型を固定した元の値比較と標準極限比較の合成則。 -/
lemma nativeLeftSectionsValueIso_comp
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (d e : JoinCone (nativeLeftSectionsDiagram P O)) (hd : IsLimitCone d) (he : IsLimitCone e) :
    nativeLeftSectionsValueIso P O hE d hd ≪≫ limitVertexIso d e hd he =
      nativeLeftSectionsValueIso P O hE e he := by
  apply CategoryTheory.Iso.ext
  change (nativeLeftSectionsValueIso P O hE d hd).hom ≫ (limitVertexIso d e hd he).hom =
    (nativeLeftSectionsValueIso P O hE e he).hom
  simp only [nativeLeftSectionsValueIso, nativeWeightedSections_leftLimitIso,
    vertexIso_transport_source_hom]
  dsimp only [nativeLeftSectionsValue, nativeLeftSectionsDiagram] at *
  rw [Category.assoc, limitVertexIsoOfDiagramEq_hom_comp]

end SerrePositivity.InfinityCategories.Sheaves

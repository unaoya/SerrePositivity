module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCoherentComponents
public import SerrePositivity.KST.SConstruction.PointedKanDiagramExtensionComponents
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyChoices

/-! # 全体の coherent な組み立てと元の選択構造射の照合
概要：全入力単体で選んだ変換の成分を、元の任意の逆射・延長の選択と比較する。
方針：全体逆の逆条件、厳密な anodyne 延長の一意性、指定因子の実三角形を使う。
規約：両端・基点・元の選択構造射を保ち、同じ点つき成分であることを証明する。
使われ方：元の BF K の Ω 条件を、全射列の coherent な変換へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 図式全体の比較逆射は、元の Whitehead 逆と同じ点つき成分。 -/
lemma oneDirectionCoherentInverseDiagramMapAt_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    componentOf (oneDirectionKanComparisonInverse r (F.obj i)) =
      componentOf (oneDirectionCoherentInverseDiagramMapAt r F i) := by
  let f : (oneDirectionKanRealizationFunctor r).obj (F.obj i) ⟶
      (boundaryKanRealizationFunctor r).obj (F.obj i) := (oneDirectionKanComparisonNat r).app (F.obj i)
  have hn := pointedKanDiagramInverse_right_component
    (fun j => oneDirectionKanRealization_kanComplex r (F.obj j))
    (fun j => boundaryKanRealization_kanComplex r (F.obj j))
    (Functor.whiskerLeft F (oneDirectionKanComparisonNat r))
    (fun j => oneDirectionReducedComparison_kan_piIsomorphism r (F.obj j)) i
  change componentOf (oneDirectionCoherentInverseDiagramMapAt r F i ≫ f) =
    componentOf (𝟙 ((boundaryKanRealizationFunctor r).obj (F.obj i))) at hn
  have ho : componentOf (oneDirectionKanComparisonInverse r (F.obj i) ≫ f) =
      componentOf (𝟙 ((boundaryKanRealizationFunctor r).obj (F.obj i))) :=
    ((piZero_eq_iff_pointedHomotopy _ _).mpr (oneDirectionKanComparisonInverse_homotopy r (F.obj i))).symm
  apply componentOf_cancel_post_piIsomorphism f (oneDirectionReducedComparison_kan_piIsomorphism r (F.obj i))
  exact ho.trans hn.symm

/-- 全体で回収した延長は、元の任意の厳密な Kan 延長の選択と同じ成分。 -/
lemma kanAssemblyCoherentDiagramMapAt_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I)
    (v : (kanAssemblyAdjointChoices r (F.obj i)) _⦋0⦌) :
    componentOf (kanAssemblyAdjointAt r (F.obj i) v) =
      componentOf (kanAssemblyCoherentDiagramMapAt r F i) :=
  pointedKanDiagramExtensionMapAt_component
    (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r)) i
    (kanAssemblyAdjointAt r (F.obj i) v) (kanAssemblyAdjointAt_fac r (F.obj i) v)

/-- 全体の組み立ての実三角形は、回収した二因子の元の点つき合成を保つ。 -/
lemma boundaryAssemblyCoherentDiagramMapAt_factor_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    componentOf (oneDirectionCoherentInverseDiagramMapAt r F i ≫
      kanAssemblyCoherentDiagramMapAt r F i) = componentOf (boundaryAssemblyCoherentDiagramMapAt r F i) :=
  pointedKanDiagramTriangle_components
    (fun j => boundaryKanRealization_kanComplex r (F.obj j))
    (fun j => oneDirectionKanRealization_kanComplex r (F.obj j))
    (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j)) _ _ _
    (boundaryAssemblyCoherentDiagramTriangle r F) i

/-- 元の任意の選択構造射は、全入力単体に自然な変換の回収成分と同じ点つき成分。 -/
lemma boundaryAssemblyCoherentDiagramMapAt_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I)
    (v : (boundaryKanAssemblyChoices r (F.obj i)) _⦋0⦌) :
    componentOf (boundaryKanAssemblyAdjointAt r (F.obj i) v) =
      componentOf (boundaryAssemblyCoherentDiagramMapAt r F i) := by
  have hi := (oneDirectionKanInverseAt_component r (F.obj i) v.1).symm.trans
    (oneDirectionCoherentInverseDiagramMapAt_component r F i)
  have he := kanAssemblyCoherentDiagramMapAt_component r F i v.2
  exact (componentOf_comp_right hi (kanAssemblyAdjointAt r (F.obj i) v.2)).trans
    ((componentOf_comp_left he (oneDirectionCoherentInverseDiagramMapAt r F i)).trans
      (boundaryAssemblyCoherentDiagramMapAt_factor_component r F i))

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.KanAssemblyEquivalence
public import SerrePositivity.KST.SConstruction.PointedKanStrictExtension
public import SerrePositivity.KST.SConstruction.PointedPiLocalized
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-! # 元の組み立て随伴の任意の Kan 模型への移送
概要：元の組み立ての随伴は、任意の anodyne 単位による Kan 模型でも全基点 π 同型。
方針：既存の標的 Kan 模型から厳密に延長し、loop の弱比較保存と元の制限式を使う。
規約：延長は弱比較の証明にだけ使う。使われ方：同じ Ex∞ による厳密 dg 組み立て。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet Spectra
open SerrePositivity.SimplicialModel

/-- 元の組み立ての随伴は、任意の標的 anodyne Kan 模型上で局所化可逆。 -/
lemma assemblyTargetAdjoint_localized_isIso_of_anodyne (r : ℕ) (X : StableModel.{u})
    {B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (j : boundaryReducedRealization (r + 1) X ⟶ B) (hj : anodyneExtensions j.right) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (((oneDirectionAssemblyAdjointNat r).app X) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map j).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}
  let b := pointedKanStrictExtension j
  let a : oneDirectionReducedRealization r X ⟶
      L.obj (PointedKanReplacement.obj (boundaryReducedRealization (r + 1) X)) :=
    (kanTargetAssemblyAdjointNat r).app X
  let _ : KanComplex (L.obj (PointedKanReplacement.obj
      (boundaryReducedRealization (r + 1) X))).right := loopSpace_kanComplex _
  let _ : KanComplex (L.obj B).right := loopSpace_kanComplex _
  have hb := pointedKanStrictExtension_piIsomorphism j
    ((Localization.inverts Q anodyneExtensions) _ hj)
  let _ : IsIso (Q.map (L.map b).right) :=
    pointed_localized_isIso_of_piIsomorphism (L.map b)
      (PointedMapping.post_piIsomorphism PointedSimplicialSet.circle b hb)
  let _ : IsIso (Q.map a.right) :=
    kanTargetAssemblyAdjoint_localized_isIso r X
  have he : a ≫ L.map b =
      (oneDirectionAssemblyAdjointNat r).app X ≫ L.map j := by
    change (((oneDirectionAssemblyAdjointNat r).app X) ≫
      L.map (PointedKanReplacement.unit.app (boundaryReducedRealization (r + 1) X))) ≫ _ = _
    erw [Category.assoc, ← L.map_comp, pointedKanStrictExtension_fac]
  have hs : IsIso (Q.map (a ≫ L.map b).right) := by
    change IsIso (Q.map (a.right ≫ (L.map b).right))
    erw [Q.map_comp]
    infer_instance
  exact (congrArg (fun q => IsIso (Q.map q.right)) he).mp hs

/-- 元の組み立て随伴の任意の anodyne Kan 延長は、全基点・全次数で π 同型。 -/
lemma assemblyAdjoint_piIsomorphism_of_anodyne_units (r : ℕ) (X : StableModel.{u})
    {U B : PointedSimplicialSet.{u}} [KanComplex U.right] [KanComplex B.right]
    (i : oneDirectionReducedRealization r X ⟶ U) (hi : anodyneExtensions i.right)
    (j : boundaryReducedRealization (r + 1) X ⟶ B) (hj : anodyneExtensions j.right)
    (a : U ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B)
    (ha : i ≫ a = (oneDirectionAssemblyAdjointNat r).app X ≫
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map j) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right := by
  let Q := AnodyneHomotopy.anodyneQ
  let _ : IsIso (Q.map i.right) := (Localization.inverts Q anodyneExtensions) _ hi
  have hs := assemblyTargetAdjoint_localized_isIso_of_anodyne r X j hj
  have hc : IsIso (Q.map i.right ≫ Q.map a.right) := by
    rw [← Q.map_comp, ← Under.comp_right, ha]
    exact hs
  exact kanPiIsomorphism_of_localized_isIso a.right ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.KST.SConstruction

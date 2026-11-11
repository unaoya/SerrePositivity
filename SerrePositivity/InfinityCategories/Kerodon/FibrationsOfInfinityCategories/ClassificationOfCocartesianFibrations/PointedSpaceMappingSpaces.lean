module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoslicePinchedIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices

/-!
概要：pointed-space と unstraightening の fiber の左写像空間表示、および右写像空間の値の回収。
方針：coslice fiber の同型を適用し、豊穣 Hom の側は単位対象からの内部 Hom で計算する。
規約：左右の写像空間の比較自体はここで仮定しない。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、Example 5.6.2.9（Tag 026S）、空間値 fiber 比較の両側。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：pointed-space 射影の fiber は一点空間からの左写像空間と同型。
方針：coslice fiber の一般の同型を 𝒮 の一点空間に適用する。
規約：頂点 s は任意の 𝒮 の頂点。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、pointed-space fiber の全次数の表示。 -/
noncomputable def pointedSpaceFiberPinchedLeftIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex s :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberPinchedLeftIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex s

/-- 概要：left unstraightening の fiber は図式の値への左写像空間と同型。
方針：引き戻しの fiber の同型と pointed-space fiber の同型を合成する。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、unstraightening の fiber の写像空間表示。 -/
noncomputable def leftUnstraighteningFiberPinchedLeftIso {C : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) c ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex (F.app (Opposite.op ⦋0⦌) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F c ≪≫
    pointedSpaceFiberPinchedLeftIso (F.app (Opposite.op ⦋0⦌) c)

/-- 概要：一点空間から Kan 複体への豊穣 Hom は元の Kan 複体と同型。
方針：Δ[0] とテンソル単位の同型を内部 Hom に写し、単位の内部 Hom を消去する。
規約：単体集合の厳密な同型であり、π₀ の計算に制限しない。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、空間値の回収の豊穣 Hom 側。 -/
noncomputable def pointKanObjectHomIso (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K ≅ K.obj := by
  let e : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
    stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit
  exact ((internalHom (C := SSet.{u})).mapIso e.symm.op).app K.obj ≪≫ unitIsoSelf K.obj

/-- 概要：𝒮 の一点空間から K への右写像空間は K の宇宙持ち上げと同値。
方針：coherent Hom 比較の逆と、一点空間からの豊穣 Hom の同型を合成する。
規約：fiber 側の左写像空間との比較は別に要する。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Construction 5.5.2.1（Tag 01ZW）、値の回収の右模型。 -/
noncomputable def pointSpaceRightMappingEquivalence (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K))
      ((SSet.uliftFunctor.{u + 1, u}).obj K.obj) := by
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject from
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K)))

/-- 概要：任意の 𝒮 の頂点への右写像空間はその頂点が表す空間と同値。
方針：coherent nerve の頂点と対象の同値で標準頂点へ書き直す。
規約：比較先は元の Kan 複体の宇宙を u+1 に持ち上げる。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、coherent な図式の値の回収。 -/
noncomputable def pointSpaceRightMappingEquivalenceAt (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex s)
      ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s).obj) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s) = s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertexEquiv.apply_symm_apply s
  rw [← hs]
  exact pointSpaceRightMappingEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject s)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

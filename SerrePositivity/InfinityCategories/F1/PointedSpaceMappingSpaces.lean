module

public import SerrePositivity.InfinityCategories.F1.CoslicePinchedIso
public import SerrePositivity.InfinityCategories.F1.CoherentHomEquivalence
public import SerrePositivity.InfinityCategories.F1.PointedSpaceFiberVertices

/-!
概要：pointed-space と unstraightening の fiber の左写像空間表示、および右写像空間の値の回収。
方針：coslice fiber の同型を適用し、豊穣 Hom の側は単位対象からの内部 Hom で計算する。
規約：左右の写像空間の比較自体はここで仮定しない。
使われ方：Kerodon Construction 5.5.2.1、Example 5.6.2.9、空間値 fiber 比較の両側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pointed-space 射影の fiber は一点空間からの左写像空間と同型。
方針：coslice fiber の一般の同型を 𝒮 の一点空間に適用する。
規約：頂点 s は任意の 𝒮 の頂点。
使われ方：Kerodon Construction 5.5.2.1、pointed-space fiber の全次数の表示。 -/
noncomputable def pointedSpaceFiberPinchedLeftIso (s : SpaceInfinity.{u} _⦋0⦌) :
    vertexFiber pointedSpaceProjection s ≅ pinchedHomLeft pointSpaceVertex s :=
  cosliceFiberPinchedLeftIso pointSpaceVertex s

/-- 概要：left unstraightening の fiber は図式の値への左写像空間と同型。
方針：引き戻しの fiber の同型と pointed-space fiber の同型を合成する。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon Example 5.6.2.9、unstraightening の fiber の写像空間表示。 -/
noncomputable def leftUnstraighteningFiberPinchedLeftIso {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection F) c ≅
      pinchedHomLeft pointSpaceVertex (F.app (Opposite.op ⦋0⦌) c) :=
  leftUnstraighteningFiberIso F c ≪≫
    pointedSpaceFiberPinchedLeftIso (F.app (Opposite.op ⦋0⦌) c)

/-- 概要：一点空間から Kan 複体への豊穣 Hom は元の Kan 複体と同型。
方針：Δ[0] とテンソル単位の同型を内部 Hom に写し、単位の内部 Hom を消去する。
規約：単体集合の厳密な同型であり、π₀ の計算に制限しない。
使われ方：Kerodon Construction 3.1.6.1、空間値の回収の豊穣 Hom 側。 -/
noncomputable def pointKanObjectHomIso (K : KanObject.{u}) :
    SimplicialCategory.sHom pointKanObject K ≅ K.obj := by
  let e : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
    stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit
  exact ((internalHom (C := SSet.{u})).mapIso e.symm.op).app K.obj ≪≫ unitIsoSelf K.obj

/-- 概要：𝒮 の一点空間から K への右写像空間は K の宇宙持ち上げと同値。
方針：coherent Hom 比較の逆と、一点空間からの豊穣 Hom の同型を合成する。
規約：fiber 側の左写像空間との比較は別に要する。
使われ方：Kerodon Theorem 4.6.7.5、Construction 5.5.2.1、値の回収の右模型。 -/
noncomputable def pointSpaceRightMappingEquivalence (K : KanObject.{u}) :
    QCatEquivalence (pinchedHom pointSpaceVertex (spaceInfinityVertex K))
      ((SSet.uliftFunctor.{u + 1, u}).obj K.obj) := by
  rw [show pointSpaceVertex = coherentNerveVertex pointKanObject from
    spaceInfinityVertex_eq_coherent pointKanObject, spaceInfinityVertex_eq_coherent]
  exact (coherentHomEquivalence pointKanObject K).symm.trans
    (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K)))

/-- 概要：任意の 𝒮 の頂点への右写像空間はその頂点が表す空間と同値。
方針：coherent nerve の頂点と対象の同値で標準頂点へ書き直す。
規約：比較先は元の Kan 複体の宇宙を u+1 に持ち上げる。
使われ方：Kerodon Construction 5.5.2.1、coherent な図式の値の回収。 -/
noncomputable def pointSpaceRightMappingEquivalenceAt (s : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (pinchedHom pointSpaceVertex s)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj) := by
  have hs : spaceInfinityVertex (spaceInfinityObject s) = s :=
    spaceInfinityVertexEquiv.apply_symm_apply s
  rw [← hs]
  exact pointSpaceRightMappingEquivalence (spaceInfinityObject s)

end SerrePositivity.InfinityCategories

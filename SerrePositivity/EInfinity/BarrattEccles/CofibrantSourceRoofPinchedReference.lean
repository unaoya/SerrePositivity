module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductReference
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantKanHammockPinched

/-!
# 実 ProductHomMap と同じ始終域を持つ元の高次比較の弱な基準射

概要：元の積単体・元の augmentation・保存済みの比較を同じ pinched Hom へ送る。
方針：元の Ex∞ 単位と cofibrant 包含の実逆データを順に合成する。
規約：基準射の弱同値性は証明する。実 ProductHomMap とのホモトピーは別工程。
使われ方：屋根 cofinal 性を全単体の具体的な比較ホモトピーへ還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductPinchedReferenceMap :
    nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
        (cofibrantHammockVertex A Y) :=
  cofibrantSourceRoofProductDegreeHammockMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (algebraReducedHammock A (cofibrantSourceRoofDegreeAlgebra A X Y b).obj
      Y.obj) ≫ cofibrantHammockPinchedReferenceMap A (cofibrantSourceRoofDegreeAlgebra A X Y b) Y

lemma cofibrantSourceRoofProductPinchedReferenceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductPinchedReferenceMap A X Y b) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
      (algebraReducedHammock A (cofibrantSourceRoofDegreeAlgebra A X Y b).obj Y.obj)) :=
    FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _))
  exact (cofibrantSourceRoofProductDegreeHammockMap_weak A X Y b).comp
    (hu.comp (cofibrantHammockPinchedReferenceMap_weak A
      (cofibrantSourceRoofDegreeAlgebra A X Y b) Y))

lemma cofibrantSourceRoofProductHomMap_weak_of_reference_homotopy
    (H : SSet.Homotopy (cofibrantSourceRoofProductHomMap A X Y b)
      (cofibrantSourceRoofProductPinchedReferenceMap A X Y b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b) := by
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts H
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  rw [h]
  exact Hammock.anodyneQ_map_isIso_of_weak _
    (cofibrantSourceRoofProductPinchedReferenceMap_weak A X Y b)

lemma cofibrantSourceRoofMap_isLeftCofinal_of_reference_homotopy
    (H : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      Nonempty (SSet.Homotopy (cofibrantSourceRoofProductHomMap A X Y b)
        (cofibrantSourceRoofProductPinchedReferenceMap A X Y b))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_productHom_weak A X Y
    (fun b => cofibrantSourceRoofProductHomMap_weak_of_reference_homotopy A X Y b (H b).some)

end SerrePositivity.EInfinity.BarrattEccles

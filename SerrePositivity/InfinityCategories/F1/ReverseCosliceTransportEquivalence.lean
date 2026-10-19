module

public import SerrePositivity.InfinityCategories.F1.CoherentReverseIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1.CoherentReversePointHomAction

/-!
概要：反転した coherent 合成の同値性から普遍 coslice 輸送の写像空間上の同値性を得る。
方針：標準輸送の終点作用を curry し、パラメーターと始終点の比較を同値の消去則で除く。
規約：任意の高次パラメーターを保ち、頂点ごとの比較には帰着しない。
使われ方：普遍 pointed-space 輸送の同値性と境界固定の表現延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance : ∀ A B : KanObject.{u}ᵒᵖ, KanComplex (SimplicialCategory.sHom A B) :=
  fun A B ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom B.unop A.unop))

/-- 概要：標準反転合成の curry が同値なら反対 nerve の普遍 coslice 輸送も同値。
方針：標準輸送と普遍輸送の関手同型で比較し、底と係数の同値を消去する。
規約：同値性は固定端点の写像空間全体から fiber 間の関手空間への実際の射に関する。
使われ方：一点 Hom の標準合成から普遍輸送の同値性を導く一般の還元。 -/
lemma parametrizedCosliceTransport_isQCatEquivalence_of_reverseComposition
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)] (X Y Z : C)
    (ha : IsQCatEquivalence (curry (coherentReverseHomComposition X Y Z))) :
    IsQCatEquivalence (parametrizedFiberTransport
      (sliceUnderProjection (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
      (SSet.opObjEquiv.symm (coherentNerveVertex Y))
      (SSet.opObjEquiv.symm (coherentNerveVertex X))) := by
  have hs := (coherentReverseSliceFiberComparison_homotopyEquivalence Y Z).isQCatEquivalence
  have ht := (coherentReverseSliceFiberComparison_homotopyEquivalence X Z).isQCatEquivalence
  have hm : IsQCatEquivalence (coherentCompositionReverseTransportFamily X Y Z).map := by
    change IsQCatEquivalence (curry (coherentReverseHomComposition X Y Z ≫
      coherentReverseSliceFiberComparison X Z))
    rw [curry_natural_right]
    exact ha.comp (ht.postcompose _)
  have hc := hm.ofFunctorIso (coherentCompositionReverseTransport_parametrizedIso X Y Z)
  change IsQCatEquivalence (coherentReverseHomIntervalMap X Y ≫
    parametrizedFiberTransport
      (sliceUnderProjection (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
      (SSet.opObjEquiv.symm (coherentNerveVertex Y))
      (SSet.opObjEquiv.symm (coherentNerveVertex X)) ≫
    (pre (coherentReverseSliceFiberComparison Y Z)).app _) at hc
  have hp := (coherentReverseHomIntervalMap_isQCatEquivalence X Y).cancel_left hc
  exact (hs.precompose _).cancel_right hp

/-- 概要：反対 Kan 圏の一点からの普遍 coslice 輸送は写像空間上で同値。
方針：一点 Hom の反転合成作用の厳密な同型性を一般の還元へ適用する。
規約：底は反対 Kan 圏の coherent nerve をさらに反転したもの。
使われ方：coherent nerve の反対同型で実際の pointed-space 射影へ同値性を移す。 -/
lemma parametrizedReverseKanPointCosliceTransport_isQCatEquivalence
    (K L : KanObject.{u}) :
    IsQCatEquivalence (parametrizedFiberTransport
      (sliceUnderProjection (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u})))))
      (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op K)))
      (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op L)))) := by
  apply parametrizedCosliceTransport_isQCatEquivalence_of_reverseComposition
    (Opposite.op L) (Opposite.op K) (Opposite.op pointKanObject)
  exact (qCatEquivalenceOfIso (asIso (curry (coherentReverseHomComposition
    (Opposite.op L) (Opposite.op K) (Opposite.op pointKanObject))))).isQCatEquivalence

end SerrePositivity.InfinityCategories

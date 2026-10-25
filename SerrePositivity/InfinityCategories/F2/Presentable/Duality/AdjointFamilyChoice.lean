module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitFamilyLifting

/-!
概要：元の二対象間で左・右関手の全単体族から随伴族を選ぶ。
方針：実単位の局所対応の厳密な切断の後に反対側の射影を続ける。
規約：二対象を固定した族であり、全 Pr の関手は別工程で構成する。
使われ方：境界を保つ族の延長と元の随伴の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：実単位の局所対応への左切断は QCat 同値。
方針：厳密な切断の等式と左射影の同値性で合成を消去する。
規約：構成済みの同じ切断を使う。
使われ方：選んだ右随伴族の同値性。 -/
lemma adjointUnitLeftSection_isQCatEquivalence (C D : PresentableInfinityObject.{u}) :
    IsQCatEquivalence (adjointUnitLeftSection C D) := by
  apply (adjointUnitLeft_isQCatEquivalence C D).cancel_right
  rw [adjointUnitLeftSection_projection]
  exact (QCatEquivalence.refl (PrLMappingSpace C D)).isQCatEquivalence

/-- 概要：実単位の局所対応への右切断は QCat 同値。
方針：厳密な切断の等式と右射影の同値性を使う。
規約：構成済みの同じ切断を使う。
使われ方：選んだ左随伴族の同値性。 -/
lemma adjointUnitRightSection_isQCatEquivalence (C D : PresentableInfinityObject.{u}) :
    IsQCatEquivalence (adjointUnitRightSection C D) := by
  apply (adjointUnitRight_isQCatEquivalence C D).cancel_right
  rw [adjointUnitRightSection_projection]
  exact (QCatEquivalence.refl (PrRMappingSpace D C)).isQCatEquivalence

/-- 概要：元の左関手の全単体族から右随伴族を選ぶ単体写像。
方針：厳密な左切断の実単位の右射影を取る。
規約：元の e1 の二つの写像空間を使う。
使われ方：左関手族に対応する右随伴族の回収。 -/
def rightAdjointMappingFamily (C D : PresentableInfinityObject.{u}) :
    PrLMappingSpace C D ⟶ PrRMappingSpace D C :=
  adjointUnitLeftSection C D ≫ adjointUnitRight C D

/-- 概要：選んだ右随伴族の単体写像は QCat 同値。
方針：厳密な左切断と右射影の同値を合成する。
規約：二対象間の写像空間に対する結論。
使われ方：全体の対応の局所比較。 -/
lemma rightAdjointMappingFamily_isQCatEquivalence (C D : PresentableInfinityObject.{u}) :
    IsQCatEquivalence (rightAdjointMappingFamily C D) :=
  (adjointUnitLeftSection_isQCatEquivalence C D).comp (adjointUnitRight_isQCatEquivalence C D)

/-- 概要：元の右関手の全単体族から左随伴族を選ぶ単体写像。
方針：厳密な右切断の実単位の左射影を取る。
規約：元の e1 の二つの写像空間を使う。
使われ方：右関手族に対応する左随伴族の回収。 -/
def leftAdjointMappingFamily (C D : PresentableInfinityObject.{u}) :
    PrRMappingSpace D C ⟶ PrLMappingSpace C D :=
  adjointUnitRightSection C D ≫ adjointUnitLeft C D

/-- 概要：選んだ左随伴族の単体写像は QCat 同値。
方針：厳密な右切断と左射影の同値を合成する。
規約：二対象間の写像空間に対する結論。
使われ方：全体の対応の逆向きの局所比較。 -/
lemma leftAdjointMappingFamily_isQCatEquivalence (C D : PresentableInfinityObject.{u}) :
    IsQCatEquivalence (leftAdjointMappingFamily C D) :=
  (adjointUnitRightSection_isQCatEquivalence C D).comp (adjointUnitLeft_isQCatEquivalence C D)

/-- 概要：選んだ右随伴族の各頂点は元の左関手の実際の右随伴。
方針：切断の左射影の等式で元の左関手を回収し、対応の指定単位から随伴を作る。
規約：元の関手を同型だけで置き換えない。
使われ方：単体写像として選んだ族と d の随伴の意味の照合。 -/
def rightAdjointMappingFamilyAdjunction {C D : PresentableInfinityObject.{u}}
    (v : PrLMappingSpace C D _⦋0⦌) :
    QCatAdjunction (leftVertexFunctor v.val)
      (rightVertexFunctor ((rightAdjointMappingFamily C D).app (Opposite.op ⦋0⦌) v).val) := by
  let x := (adjointUnitLeftSection C D).app (Opposite.op ⦋0⦌) v
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app (adjointUnitLeftSection_projection C D) (Opposite.op ⦋0⦌)) v
  change (adjointUnitLeft C D).app (Opposite.op ⦋0⦌) x = v at hx
  have hL := congrArg (fun z : PrLMappingSpace C D _⦋0⦌ ↦ leftVertexFunctor z.val) hx
  change unitLeftFunctor x.val.val = leftVertexFunctor v.val at hL
  have a := adjointUnitAdjunction x
  rw [hL] at a
  exact a

/-- 概要：選んだ左随伴族の各頂点は元の右関手の実際の左随伴。
方針：切断の右射影の等式と対応の指定単位を使う。
規約：元の右関手を厳密に保持する。
使われ方：逆向きに選んだ族と随伴の意味の照合。 -/
def leftAdjointMappingFamilyAdjunction {C D : PresentableInfinityObject.{u}}
    (w : PrRMappingSpace D C _⦋0⦌) :
    QCatAdjunction
      (leftVertexFunctor ((leftAdjointMappingFamily C D).app (Opposite.op ⦋0⦌) w).val)
      (rightVertexFunctor w.val) := by
  let x := (adjointUnitRightSection C D).app (Opposite.op ⦋0⦌) w
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app (adjointUnitRightSection_projection C D) (Opposite.op ⦋0⦌)) w
  change (adjointUnitRight C D).app (Opposite.op ⦋0⦌) x = w at hx
  have hR := congrArg (fun z : PrRMappingSpace D C _⦋0⦌ ↦ rightVertexFunctor z.val) hx
  change unitRightFunctor x.val.val = rightVertexFunctor w.val at hR
  have a := adjointUnitAdjunction x
  rw [hR] at a
  exact a

end SerrePositivity.InfinityCategories.F2.Presentable.Duality

module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LocalMappingEquivalence

/-!
概要：境界で指定した随伴単位の族を保つ相対持ち上げと、局所射影の厳密な切断。
方針：両局所射影の trivial Kan fibration 性を全単射に対する持ち上げ性として使う。
規約：パラメータの充填性や追加の同値の存在を仮定しない。
使われ方：全体の対応の単体を境界から延長するための局所入力。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：指定した左関手族と境界の実単位族を同時に保持して延長する。
方針：左局所射影の全単射に対する持ち上げ性を使う。
規約：パラメータ A・B は任意の単体集合。
使われ方：既存の境界を固定した随伴単位族の構成。 -/
lemma adjointUnitLeft_extend (C D : PresentableInfinityObject.{u})
    {A B : SSet.{u + 1}} (i : A ⟶ B) [Mono i]
    (f : A ⟶ AdjointUnitMappingSpace C D) (g : B ⟶ PrLMappingSpace C D)
    (h : f ≫ adjointUnitLeft C D = i ≫ g) :
    ∃ t : B ⟶ AdjointUnitMappingSpace C D, i ≫ t = f ∧ t ≫ adjointUnitLeft C D = g := by
  haveI : HasLiftingProperty i (adjointUnitLeft C D) :=
    TrivialKanFibration.mem (p := adjointUnitLeft C D) i inferInstance
  let sq : CommSq f i (adjointUnitLeft C D) g := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：指定した右関手族と境界の実単位族を同時に保持して延長する。
方針：右局所射影の全単射に対する持ち上げ性を使う。
規約：パラメータ A・B は任意の単体集合。
使われ方：右側で既存の境界を固定した随伴単位族の構成。 -/
lemma adjointUnitRight_extend (C D : PresentableInfinityObject.{u})
    {A B : SSet.{u + 1}} (i : A ⟶ B) [Mono i]
    (f : A ⟶ AdjointUnitMappingSpace C D) (g : B ⟶ PrRMappingSpace D C)
    (h : f ≫ adjointUnitRight C D = i ≫ g) :
    ∃ t : B ⟶ AdjointUnitMappingSpace C D, i ≫ t = f ∧ t ≫ adjointUnitRight C D = g := by
  haveI : HasLiftingProperty i (adjointUnitRight C D) :=
    TrivialKanFibration.mem (p := adjointUnitRight C D) i inferInstance
  let sq : CommSq f i (adjointUnitRight C D) g := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：元の左写像空間から実単位の局所対応への厳密な切断。
方針：全境界を持ち上げる射の切断を構成済みの定理から選ぶ。
規約：頂点だけの選択ではなく全単体に作用する射。
使われ方：左関手族から元の右随伴族と実単位を選ぶ。 -/
def adjointUnitLeftSection (C D : PresentableInfinityObject.{u}) :
    PrLMappingSpace C D ⟶ AdjointUnitMappingSpace C D :=
  Classical.choose (trivialKanFibration_exists_section (adjointUnitLeft C D))

/-- 概要：左切断を元の左写像空間へ戻すと厳密な恒等射。
方針：切断の選択に付随する等式を使う。
規約：同じ左関手族を全単体で保持する。
使われ方：選んだ随伴の元の左関手の回収。 -/
lemma adjointUnitLeftSection_projection (C D : PresentableInfinityObject.{u}) :
    adjointUnitLeftSection C D ≫ adjointUnitLeft C D = 𝟙 (PrLMappingSpace C D) :=
  Classical.choose_spec (trivialKanFibration_exists_section (adjointUnitLeft C D))

/-- 概要：元の右写像空間から実単位の局所対応への厳密な切断。
方針：全境界を持ち上げる右射影の切断を選ぶ。
規約：元の右関手の全高次単体を保持する。
使われ方：右関手族から左随伴族と実単位を選ぶ。 -/
def adjointUnitRightSection (C D : PresentableInfinityObject.{u}) :
    PrRMappingSpace D C ⟶ AdjointUnitMappingSpace C D :=
  Classical.choose (trivialKanFibration_exists_section (adjointUnitRight C D))

/-- 概要：右切断を元の右写像空間へ戻すと厳密な恒等射。
方針：切断の選択の仕様を使う。
規約：同じ右関手族を全単体で保持する。
使われ方：選んだ随伴の元の右関手の回収。 -/
lemma adjointUnitRightSection_projection (C D : PresentableInfinityObject.{u}) :
    adjointUnitRightSection C D ≫ adjointUnitRight C D = 𝟙 (PrRMappingSpace D C) :=
  Classical.choose_spec (trivialKanFibration_exists_section (adjointUnitRight C D))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality

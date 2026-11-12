module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：一点空間からの内部 Hom を取る Kan 値豊穣自己関手。
方針：高次の Hom の作用を内部 Hom の合成の curry として構成する。
規約：通常の射への自然性に制限せず、全ての Hom 単体に作用させる。
使われ方：Kerodon §4.6.7（Tag 01LA）、Corollary 5.6.0.6（Tag 028T）、普遍 left fibration の係数の高次の自然性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：一点空間からの内部 Hom は Kan 複体の単体的圏の豊穣自己関手。
方針：内部 Hom の合成を curry し、単位と合成則を各パラメーターで評価する。
規約：対象の値は既存の一点空間からの豊穣 Hom と定義的に一致する。
使われ方：Kerodon §4.6.7（Tag 01LA）、Corollary 5.6.0.6（Tag 028T）、coherent な係数の正規化。 -/
noncomputable def kanPointHomEnriched :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj K := ⟨(ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj).obj K.obj, inferInstance⟩
  map K L := curry (MonoidalClosed.comp _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj K.obj L.obj)
  map_id K := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, t⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    change f.app m (α ≫ 𝟙 m) x = f.app m α x
    rw [Category.comp_id]
  map_comp K L M := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g, h⟩
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：一点空間からの Hom の標準同型は高次の Hom の作用についても自然。
方針：内部 Hom の合成と標準同型をパラメーター単体ごとに評価する。
規約：各成分は既存の pointKanObjectHomIso の順方向そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、係数の同型を任意の coherent な図式へ移す。 -/
noncomputable def kanPointHomEnrichedComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison kanPointHomEnriched
      (EnrichedFunctor.id SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) := by
  refine ⟨(fun K ↦ show kanPointHomEnriched.obj K ⟶ K from (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).hom), ?_⟩
  intro K L
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  rfl

/-- 概要：一点空間からの内部 Hom の豊穣作用を空間の coherent nerve 上へ移す。
方針：構成した豊穣自己関手に coherent nerve を適用する。
規約：対象は一点空間からの内部 Hom であり、全ての高次の射にも作用する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、任意の coherent な図式の係数の正規化。 -/
noncomputable def kanPointHomInfinityMap : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap kanPointHomEnriched

/-- 概要：一点空間からの内部 Hom を取る空間の自己写像は恒等写像と関手同型。
方針：標準同型の豊穣な比較を coherent な比較へ移し、各成分の同型性を使う。
規約：各対象の同型の存在だけでなく関手空間内の同型を与える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、任意の coherent な図式の係数の高次の整合性。 -/
noncomputable def kanPointHomInfinityComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso kanPointHomInfinityMap.{u} (𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso kanPointHomEnrichedComparison
    (fun K ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K)).isQCatEquivalence)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id] at h
  exact h

/-- 概要：任意の空間値 coherent 図式から一点空間の Hom を取った図式は元の図式と関手同型。
方針：空間全体の標準比較を元の図式に沿って引き戻す。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の図式の左 fiber の係数を自然に正規化する。 -/
noncomputable def kanPointHomDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ kanPointHomInfinityMap) F := by
  have h := kanPointHomInfinityComparisonIso.precomp F
  rw [Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

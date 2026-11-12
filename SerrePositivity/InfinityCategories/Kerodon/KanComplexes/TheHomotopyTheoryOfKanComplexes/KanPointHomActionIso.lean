module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanPointHomEnriched

/-!
概要：一点 Hom に対する豊穣な合成作用は写像空間全体の同型。
方針：既存の一点 Hom の標準同型による豊穣な自然性を curry する。
規約：標準合成の実際の Hom 上の射について証明する。
使われ方：標準合成輸送と普遍 pointed-space 輸送の比較の同値性。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：一点 Hom の豊穣作用を標準同型で戻すと内部 Hom の前合成となる。
方針：豊穣な比較の評価の自然性を curry の自然性で表示する。
規約：K と L の写像空間の全ての高次単体を保持する。
使われ方：一点 Hom の合成作用の同型性。 -/
lemma kanPointHomEnriched_map_post (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L ≫
      (ihom (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso L).hom =
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).hom).app L.obj := by
  apply uncurry_injective
  rw [uncurry_natural_right]
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).hom ▷ SimplicialCategory.sHom K L) ≫
        uncurry (𝟙 (SimplicialCategory.sHom K L)) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnrichedComparison.property K L).symm
    _ = uncurry (𝟙 (SimplicialCategory.sHom K L) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).hom).app L.obj) :=
      (uncurry_pre_app L.obj (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).hom).symm
    _ = _ := by rw [Category.id_comp]

/-- 概要：一点 Hom に対する豊穣合成の写像空間上の作用は同型。
方針：標準同型による後合成を消去し、前合成の同型性を使う。
規約：元の Kan 複体の間の写像の高次パラメーター全体での同型。
使われ方：普遍輸送の同値性への標準合成側の入力。 -/
instance kanPointHomEnriched_map_isIso (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L ≫
      (ihom (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso L).hom) := by
    rw [kanPointHomEnriched_map_post]
    change IsIso (((internalHom (C := SSet.{u})).mapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).op).app L.obj).hom
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ihom (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso L).hom)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

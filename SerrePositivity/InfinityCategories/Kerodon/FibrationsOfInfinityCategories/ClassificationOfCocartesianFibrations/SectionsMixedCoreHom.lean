module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionsNaturality

/-!
概要：定義域の制限と同じ cocartesian 関手の混合作用を、QCat の豊穣 Hom へ移す。
方針：元の混合作用に core 関手を適用し、元の単位・混合合成を保つ。
規約：各 Hom の高次パラメーターを保ち、可逆な変換の作用を同じ core に取る。
使われ方：二つの添字を同時に動かす Cat∞ 値の対角評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の cocartesian section の quasicategory を QCat の対象に束ねる。 -/
def cocartesianSectionsQCatObject {B : SSet.{u}} (a : Over B)
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p.val.hom a.hom, inferInstance⟩

/-- 元の混合作用の core により、cocartesian 関手と定義域を同時に動かす。 -/
def cocartesianSectionsMixedCoreHom {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B) :
    SimplicialCategory.sHom p q ⟶
      SimplicialCategory.sHom (cocartesianSectionsQCatObject b p)
        (cocartesianSectionsQCatObject a q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedHom f p.val q.val)

/-- core に移した同じ混合作用は、元の両恒等射の豊穣単位を保つ。 -/
lemma cocartesianSectionsMixedCoreHom_id {B : SSet.{u}} (a : Over B)
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B) :
    eId SSet p ≫ cocartesianSectionsMixedCoreHom (𝟙 a) p p =
      eId SSet (cocartesianSectionsQCatObject a p) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n s) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedHom_id a p.val)

/-- 元の混合合成の等式は、両側の core の豊穣合成の等式として保たれる。 -/
lemma cocartesianSectionsMixedCoreHom_comp {B : SSet.{u}} {a b c : Over B}
    (f : b ⟶ a) (g : c ⟶ b) (p q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B) :
    eComp SSet p q r ≫ cocartesianSectionsMixedCoreHom (g ≫ f) p r =
      (cocartesianSectionsMixedCoreHom f p q ⊗ₘ cocartesianSectionsMixedCoreHom g q r) ≫
        eComp SSet (cocartesianSectionsQCatObject a p) (cocartesianSectionsQCatObject b q)
          (cocartesianSectionsQCatObject c r) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨h, k⟩
  apply Subtype.ext
  exact congrArg (fun m ↦ m.app n (h.val, k.val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedHom_comp f g p.val q.val r.val)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMixedHom

/-!
概要：strict transport 図式の混合評価を QCat の core Hom に移す。
方針：各値の充填性を元の fibration による表示から回収し、混合作用に core 関手を適用する。
規約：全変換空間の core の元の作用を使う。
使われ方：Cat∞ 値関手への対角評価と中間比較の実現。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- strict transport として表示された図式の各値は quasicategory。 -/
instance cocartesianTransportDiagramObject_value_quasicategory
    {C : Type u} [Category.{u} C] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramObject C) (c : C) :
    Quasicategory (F.val.obj c) := by
  obtain ⟨p, hp⟩ := F.property
  rw [← hp]
  infer_instance

/-- 図式の各値を元の quasicategory として束ねる。 -/
def cocartesianTransportDiagramValue {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) (c : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  ⟨F.val.obj c, cocartesianTransportDiagramObject_value_quasicategory F c⟩

/-- 図式の底の射と元の変換空間を同時に評価した、core 上の作用。 -/
def cocartesianTransportDiagramMixedHom {C : Type u} [Category.{u} C] {c d : C}
    (f : c ⟶ d) (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) :
    SimplicialCategory.sHom F G ⟶
      SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f F.val G.val)

/-- 元の混合作用の単位則は core 上でも同じ単位則。 -/
lemma cocartesianTransportDiagramMixedHom_id {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) (c : C) :
    eId SSet F ≫ cocartesianTransportDiagramMixedHom (𝟙 c) F F =
      eId SSet (cocartesianTransportDiagramValue F c) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n s) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_id F.val c)

/-- 元の混合合成の等式は core の豊穣合成の等式として保たれる。 -/
lemma cocartesianTransportDiagramMixedHom_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) (F G H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) :
    eComp SSet F G H ≫ cocartesianTransportDiagramMixedHom (f ≫ g) F H =
      (cocartesianTransportDiagramMixedHom f F G ⊗ₘ
        cocartesianTransportDiagramMixedHom g G H) ≫
          eComp SSet (cocartesianTransportDiagramValue F c)
            (cocartesianTransportDiagramValue G d) (cocartesianTransportDiagramValue H e) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨h, k⟩
  apply Subtype.ext
  exact congrArg (fun m ↦ m.app n (h.val, k.val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_comp f g F.val G.val H.val)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

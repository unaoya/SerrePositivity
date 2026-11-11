module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace

/-!
概要：相対関手単体集合の前合成と、その恒等・合成則。
方針：内部 Hom の前合成を、後合成の fiber の固定条件に沿って制限する。
規約：底の図式も前合成で引き戻す。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、undercategory に関する strict transport の射。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：パラメータ始域の射は底を引き戻した相対関手単体集合への前合成を与える。
方針：内部 Hom の前合成の自然性を用いて fiber へ持ち上げる。
規約：p と i の充填性や単射性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、undercategory の反変性からの共変 transport。 -/
def relativeFunctorPre {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (i ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre i).app E) (by
    rw [Category.assoc, ← (pre i).naturality p, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：相対前合成の包含後の射は通常の内部 Hom の前合成。
方針：fiber への持ち上げの定義を計算する。
規約：底の図式は i≫a。
使われ方：Kerodon §5.3.1（Tag 035D）、相対前合成の等式の検査。 -/
lemma relativeFunctorPre_ι {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    relativeFunctorPre p a i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app E := rfl

/-- 概要：相対前合成は恒等射を恒等射へ写す。
方針：fiber の包含後に内部 Hom の恒等則を使う。
規約：固定図式の等式は単体集合の合成の定義に沿って同定する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の関手の単位則。 -/
lemma relativeFunctorPre_id {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    relativeFunctorPre p a (𝟙 A) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre (𝟙 A)).app E =
    𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 概要：相対前合成は射の合成を逆順の前合成へ写す。
方針：fiber の包含後に内部 Hom の前合成の合成則を使う。
規約：i の後に j で制限する合成は j≫i による制限。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の関手の合成則。 -/
lemma relativeFunctorPre_comp {A D T E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (j : T ⟶ D) :
    relativeFunctorPre p a i ≫ relativeFunctorPre p (i ≫ a) j =
      relativeFunctorPre p a (j ≫ i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom T).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((j ≫ i) ≫ a))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app E) ≫
      (pre j).app E = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre (j ≫ i)).app E
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

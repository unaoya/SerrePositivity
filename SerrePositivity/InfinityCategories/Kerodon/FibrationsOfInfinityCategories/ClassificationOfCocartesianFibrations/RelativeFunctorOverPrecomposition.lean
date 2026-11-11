module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：固定した射影への相対関手空間を底上の対象の反変関手にする。
方針：底上の射の前合成を内部 Hom の fiber へ制限し、包含後に恒等・合成を確認する。
規約：底上の可換性を型の移送にせず、fiber への持ち上げの条件として使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底上の同値による相対写像空間の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の射は固定した射影への相対関手空間の前合成を与える。
方針：内部 Hom の前合成の自然性と底上の可換性を使い、指定した fiber へ持ち上げる。
規約：射影 p と底上の射の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の定義域の比較。 -/
def relativeFunctorOverPre {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b.hom ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre f.left).app E) (by
    rw [Category.assoc, ← (pre f.left).naturality p, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f.left ≫ b.hom)) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom)
    rw [f.w])

/-- 概要：底上の前合成を相対関手空間の包含へ合成すると通常の前合成になる。
方針：fiber への持ち上げの射の計算則を用いる。
規約：始域の底の図式は b.hom、終域は a.hom。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対前合成の等式の検査。 -/
lemma relativeFunctorOverPre_ι {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    relativeFunctorOverPre p f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom b.left).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b.hom) ≫ (pre f.left).app E := rfl

/-- 概要：底上の恒等射の前合成は相対関手空間の恒等射。
方針：包含へ合成し、内部 Hom の恒等射に沿う前合成を計算する。
規約：底上の対象 a は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の関手の単位則。 -/
lemma relativeFunctorOverPre_id {E B : SSet.{u}} (p : E ⟶ B) (a : Over B) :
    relativeFunctorOverPre p (𝟙 a) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a.hom) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [relativeFunctorOverPre_ι]
  change _ ≫ (pre (𝟙 a.left)).app E = _
  rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 概要：底上の射の前合成は合成順序を反転する。
方針：包含後に内部 Hom の前合成の合成則を使う。
規約：f の後に g を合成する底上の射を、g の前合成の後に f の前合成へ写す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の関手の合成則。 -/
lemma relativeFunctorOverPre_comp {E B : SSet.{u}} (p : E ⟶ B) {a b c : Over B}
    (f : a ⟶ b) (g : b ⟶ c) :
    relativeFunctorOverPre p (f ≫ g) = relativeFunctorOverPre p g ≫ relativeFunctorOverPre p f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  simp only [Category.assoc, relativeFunctorOverPre_ι]
  rw [← Category.assoc, relativeFunctorOverPre_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map]
  rfl

/-- 概要：固定射影への相対関手空間は底上の単体集合の反変関手。
方針：各対象を相対関手空間に、射を前合成に写す。
規約：left fibration の場合には各値は Kan 複体となる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の相対写像空間の定義域に関する関手性。 -/
def relativeFunctorOverFunctor {E B : SSet.{u}} (p : E ⟶ B) : (Over B)ᵒᵖ ⥤ SSet.{u} where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a.unop.hom
  map f := relativeFunctorOverPre p f.unop
  map_id a := relativeFunctorOverPre_id p a.unop
  map_comp f g := relativeFunctorOverPre_comp p g.unop f.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

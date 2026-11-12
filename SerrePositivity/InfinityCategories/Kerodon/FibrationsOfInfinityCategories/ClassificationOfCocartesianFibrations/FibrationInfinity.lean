module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeUnitHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreProduct
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：固定した底上の cocartesian fibrations と、cocartesian 辺を保つ関手の ∞ 圏。
方針：全相対関手の全部分複体を豊穣 Hom とし、core 関手で可逆な変換だけを残す。
規約：Hom の全体を Kan と仮定せず、証明済みの quasicategory の core を取る。
使われ方：Cat∞ 値 straightening の実際の fibration 側。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- cocartesian な相対関手 ∞ 圏を Hom とする、core 移送前の豊穣構造。 -/
instance cocartesianFibrationObject_enrichedCategory (B : SSet.{u}) :
    EnrichedCategory SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B) where
  Hom p q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p.val.hom q.val.hom
  id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorIdentity p.val
  comp p q r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition p.val q.val r.val
  id_comp p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorIdentity_comp p.val q.val
  comp_id p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition_id p.val q.val
  assoc p q r s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorComposition_assoc p.val q.val r.val s.val

/-- 通常の cocartesian な底上の射と、豊穣 Hom の零単体は厳密に対応する。 -/
instance cocartesianFibrationObject_simplicialCategory (B : SSet.{u}) :
    SimplicialCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B) where
  homEquiv {p q} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorHomEquiv p.val q.val
  homEquiv_id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorHomEquiv_id p.val
  homEquiv_comp {p q r} f g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorHomEquiv_comp f g

/-- core 移送前の各相対関手 Hom は、射影の inner fibration 性により quasicategory。 -/
instance cocartesianFibrationObject_sHom_quasicategory {B : SSet.{u}}
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B) : Quasicategory (SimplicialCategory.sHom p q) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p.val.hom q.val.hom))

/-- 元の相対関手 Hom の core を豊穣 Hom とする、cocartesian fibrations の単体的圏。 -/
def CocartesianFibrationCategory (B : SSet.{u}) : Type (u + 1) :=
  TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B)

/-- core の豊穣構造への移送は、元の辺を保つ通常の底上の射を保持する。 -/
instance cocartesianFibrationCategory_category (B : SSet.{u}) :
    Category.{u} (CocartesianFibrationCategory B) :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B)))

/-- cocartesian 関手の相対 Hom の core により、同じ通常の圏を単体的に豊穣化する。 -/
instance cocartesianFibrationCategory_simplicialCategory (B : SSet.{u}) :
    SimplicialCategory (CocartesianFibrationCategory B) :=
  TransportEnrichment.enrichedOrdinaryCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject B)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 分類の豊穣 Hom は、元の cocartesian な相対関手の全空間の core そのもの。 -/
lemma cocartesianFibrationCategory_sHom {B : SSet.{u}}
    (p q : CocartesianFibrationCategory B) :
    SimplicialCategory.sHom p q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p.val.hom q.val.hom) : SSet.{u}) := rfl

/-- 実際の cocartesian な底上の相対関手の core は Kan 複体。 -/
instance cocartesianFibrationCategory_sHom_kanComplex {B : SSet.{u}}
    (p q : CocartesianFibrationCategory B) : KanComplex (SimplicialCategory.sHom p q) := by
  rw [cocartesianFibrationCategory_sHom]
  infer_instance

/-- cocartesian な底上の関手と可逆な相対変換から構成する、cocartesian fibrations の ∞ 圏。 -/
def CocartesianFibrationInfinity (B : SSet.{u}) : SSet.{u + 1} :=
  SimplicialNerve (CocartesianFibrationCategory B)

/-- 元の相対関手の core の局所 Kan 性から、fibration 側の分類対象は quasicategory。 -/
instance cocartesianFibrationInfinity_quasicategory (B : SSet.{u}) :
    Quasicategory (CocartesianFibrationInfinity B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (CocartesianFibrationCategory B)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

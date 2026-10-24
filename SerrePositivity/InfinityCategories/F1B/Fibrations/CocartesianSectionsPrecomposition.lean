module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianSections

/-!
概要：底上の cocartesian section の制限とその恒等・合成則。
方針：元の相対関手空間の前合成が頂点条件を保つことを使う。
規約：前合成の始域の射には充填性や単射性を要求しない。
使われ方：一般の strict transport の射と関手性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories

/-- 概要：相対関手の頂点からの回収は底上の前合成と可換。
方針：頂点を実際の射で表し、前合成の頂点の計算則を使う。
規約：底の固定条件は底上の射の可換性から得る。
使われ方：cocartesian section の頂点条件の制限による保存。 -/
lemma relativeFunctorOfVertex_overPre {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (i : a ⟶ b) (v : (relativeFunctorSpace p b.hom) _⦋0⦌) :
    SerrePositivity.InfinityCategories.relativeFunctorOfVertex p a.hom
      ((relativeFunctorOverPre p i).app (Opposite.op ⦋0⦌) v) =
        i.left ≫ SerrePositivity.InfinityCategories.relativeFunctorOfVertex p b.hom v := by
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex p b.hom v
  rw [relativeFunctorOverPre_vertex, SerrePositivity.InfinityCategories.relativeFunctorOfVertex_vertex,
    SerrePositivity.InfinityCategories.relativeFunctorOfVertex_vertex]

/-- 概要：底上の前合成は cocartesian section の条件を保つ。
方針：前合成した各辺は元の定義域の辺の像である。
規約：元の定義域の全ての辺に cocartesian 性を要求したことを使う。
使われ方：全部分複体への前合成の持ち上げ。 -/
lemma isCocartesianSection_overPre {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (i : a ⟶ b) (v : (relativeFunctorSpace p b.hom) _⦋0⦌)
    (hv : SerrePositivity.InfinityCategories.IsCocartesianSection p b.hom v) :
    SerrePositivity.InfinityCategories.IsCocartesianSection p a.hom ((relativeFunctorOverPre p i).app (Opposite.op ⦋0⦌) v) := by
  intro e
  rw [relativeFunctorOfVertex_overPre]
  exact hv (i.left.app (Opposite.op ⦋1⦌) e)

/-- 概要：底上の射による cocartesian section の制限。
方針：相対前合成が頂点条件を保つので全部分複体へ持ち上げる。
規約：制限の向きは底上の射の逆向き。
使われ方：strict transport の undercategory に沿う前合成。 -/
def cocartesianSectionsPre {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (i : a ⟶ b) : SerrePositivity.InfinityCategories.cocartesianSections p b.hom ⟶
      SerrePositivity.InfinityCategories.cocartesianSections p a.hom :=
  fullSubcomplexLift (SerrePositivity.InfinityCategories.IsCocartesianSection p a.hom)
    (SerrePositivity.InfinityCategories.cocartesianSectionsι p b.hom ≫ relativeFunctorOverPre p i)
    (fun v ↦ isCocartesianSection_overPre p i v.val (SerrePositivity.InfinityCategories.cocartesianSections_vertex p b.hom v))

/-- 概要：section の制限の包含後の射は通常の相対前合成。
方針：全部分複体の持ち上げの計算則。
規約：厳密な射の等式。
使われ方：section の制限の関手性の確認。 -/
lemma cocartesianSectionsPre_ι {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (i : a ⟶ b) :
    cocartesianSectionsPre p i ≫ SerrePositivity.InfinityCategories.cocartesianSectionsι p a.hom =
      SerrePositivity.InfinityCategories.cocartesianSectionsι p b.hom ≫ relativeFunctorOverPre p i := rfl

/-- 概要：cocartesian section の恒等射による制限は恒等射。
方針：包含後に通常の相対前合成の恒等則を使う。
規約：自然同型ではなく等式。
使われ方：strict transport の関手の単位則。 -/
lemma cocartesianSectionsPre_id {E B : SSet.{u}} (p : E ⟶ B) (a : Over B) :
    cocartesianSectionsPre p (𝟙 a) = 𝟙 _ := by
  apply (cancel_mono (SerrePositivity.InfinityCategories.cocartesianSectionsι p a.hom)).1
  rw [cocartesianSectionsPre_ι, relativeFunctorOverPre_id,
    Category.comp_id, Category.id_comp]

/-- 概要：cocartesian section の制限は合成を逆順に保つ。
方針：包含後に元の相対関手の前合成の合成則を使う。
規約：i の後に j を合成する底上の射。
使われ方：strict transport の関手の合成則。 -/
lemma cocartesianSectionsPre_comp {E B : SSet.{u}} (p : E ⟶ B)
    {a b c : Over B} (i : a ⟶ b) (j : b ⟶ c) :
    cocartesianSectionsPre p j ≫ cocartesianSectionsPre p i =
      cocartesianSectionsPre p (i ≫ j) := by
  apply (cancel_mono (SerrePositivity.InfinityCategories.cocartesianSectionsι p a.hom)).1
  rw [Category.assoc, cocartesianSectionsPre_ι, ← Category.assoc,
    cocartesianSectionsPre_ι, Category.assoc, ← relativeFunctorOverPre_comp,
    cocartesianSectionsPre_ι]

end SerrePositivity.InfinityCategories

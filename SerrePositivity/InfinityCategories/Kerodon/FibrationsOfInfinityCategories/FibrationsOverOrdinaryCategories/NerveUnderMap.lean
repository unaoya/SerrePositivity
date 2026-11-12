module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute


/-!
概要：通常の圏上の left fibration の Kan 値 strict transport 表現。
方針：各 undercategory の nerve 上の相対関手単体集合を取り、射には前合成を使う。
規約：left fibration の全ての辺は cocartesian なので、追加の頂点制限は不要。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、空間値 strict transport の対象と射。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の射から undercategory の nerve の反変な射を作る。
方針：Under.map の nerve を取る。
規約：f:c→d に対し nerve(d/C) から nerve(c/C) へ写す。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の共変な射の前合成の始域。 -/
@[kerodon 035J]
def nerveUnderMap {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    nerve (Under d) ⟶ nerve (Under c) := nerveMap (Under.map f)

/-- 概要：undercategory の nerve の射は底 C の nerve への射影を保つ。
方針：under の射の標的を忘れる関手の定義を計算する。
規約：底の図式の整合性は厳密な等式。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の相対関手空間の制限。 -/
lemma nerveUnderMap_projection {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    nerveUnderMap f ≫ nerveMap (Under.forget c) = nerveMap (Under.forget d) := rfl

/-- 概要：undercategory の nerve の反変な射は恒等射を保つ。
方針：Under.map の恒等則を nerve に写す。
規約：自然同型ではなく射の等式を使う。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の単位則。 -/
lemma nerveUnderMap_id {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap (𝟙 c) = 𝟙 (nerve (Under c)) := by
  unfold nerveUnderMap
  rw [Under.mapId_eq]
  rfl

/-- 概要：undercategory の nerve の射は合成を逆順に保つ。
方針：Under.map の合成の等式を nerve に写す。
規約：f の後に g を合成する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の合成則。 -/
lemma nerveUnderMap_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) : nerveUnderMap (f ≫ g) = nerveUnderMap g ≫ nerveUnderMap f := by
  unfold nerveUnderMap
  rw [Under.mapComp_eq]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

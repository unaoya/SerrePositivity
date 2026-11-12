module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import Mathlib.CategoryTheory.EqToHom

/-!
概要：単射である添字の射による Bousfield–Kan 重みの遷移は単射。
方針：over 圏の後合成の対象の単射性と忠実性を、全射列の単射性へ移す。
規約：通常の射の Mono 性と単体集合の射の Mono 性を区別する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一脚の fibration 性による end の充填。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：対象上で単射な忠実関手の nerve は単射。
方針：包含後の射列の等式から対象を回収し、忠実性で元の射を回収する。
規約：充満性や圏の Kan 性は不要。
使われ方：Kerodon 7.5.3（Tag 03AP） の重みの遷移の単射性。 -/
lemma nerveMap_mono_of_faithful (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) : Mono (nerveMap F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  change a ⋙ F = b ⋙ F at h
  have ho (i) : a.obj i = b.obj i := hF (Functor.congr_obj h i)
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  apply F.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_map, Functor.comp_obj]
    using (Functor.congr_hom h f)
/-- 概要：単射への後合成による over 圏の関手は対象上で単射。
方針：台の対象の等式を取り、三角形の等式の後ろの単射を消去する。
規約：対象の等式を使い、同型への持ち上げで代用しない。
使われ方：Kerodon 7.5.3（Tag 03AP） の Bousfield–Kan 重みの遷移。 -/
lemma overMap_obj_injective {x y : C} (f : x ⟶ y) [Mono f] :
    Function.Injective (Over.map f).obj := by
  intro a b h
  have hl : a.left = b.left := congrArg (fun z : Over y => z.left) h
  apply CostructuredArrow.obj_ext a b hl
  apply (cancel_mono f).1
  simpa only [Functor.id_map, Category.assoc, Over.eqToHom_left, Over.map_obj_hom]
    using (Over.w (eqToHom h))
/-- 概要：添字圏の単射に沿う Bousfield–Kan 重みの遷移は単射。
方針：後合成の対象の単射性と、over 圏の射の左成分による忠実性を nerve へ移す。
規約：添字圏とその Hom は同じ宇宙。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一脚が fibration の cospan の重み。 -/
lemma bousfieldKanWeight_map_mono {x y : C} (f : x ⟶ y) [Mono f] :
    Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C).map f) := by
  have : (Over.map f).Faithful :=
    { map_injective := fun {a b} g h e => by
        apply Over.OverMorphism.ext
        exact congrArg (fun k : (Over.map f).obj a ⟶ (Over.map f).obj b => k.left) e }
  exact nerveMap_mono_of_faithful (Over.map f) (overMap_obj_injective f)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

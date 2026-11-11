module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveTerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeConeAnodyne

/-!
概要：cospan の右端の over 圏から中央の over 圏への nerve の遷移は anodyne。
方針：右端に入る射の可逆性、右脚の非可逆性と単射性を確認し、終対象を付加する分解を使う。
規約：係数の宇宙に合わせて AsSmall.{u} WalkingCospan を使う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、一脚だけが fibration の引き戻しの重みの相対境界。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：入る射が全て可逆な対象の over 圏では恒等射の対象が始対象。
方針：構造射の逆射を三角形の射として使い、一意性は可逆射を後から消去して示す。
規約：over 圏の各対象の構造射の IsIso 性を明示的に入力とする。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
noncomputable def overId_initial_of_all_isIso (x : C) (hx : ∀ a : Over x, IsIso a.hom) :
    IsInitial (Over.mk (𝟙 x)) := by
  refine IsInitial.ofUniqueHom (fun a => ?_) ?_
  · have := hx a
    exact Over.homMk (inv a.hom) (by simp)
  · intro a f
    have := hx a
    apply Over.OverMorphism.ext
    apply (cancel_mono a.hom).1
    rw [Over.w]
    simp
/-- 概要：可逆な構造射だけを持つ over 圏から非可逆射への後合成の像は恒等射を含まない。
方針：像の構造射が可逆なら元の構造射を消去して後合成の射も可逆になることを使う。
規約：後合成の射の非可逆性と各構造射の可逆性を明示する。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma overMap_misses_id {x y : C} (f : x ⟶ y) (hnot : ¬ IsIso f)
    (hx : ∀ a : Over x, IsIso a.hom) (a : Over x) :
    (Over.map f).obj a ≠ Over.mk (𝟙 y) := by
  intro h
  have : IsIso ((Over.map f).obj a).hom := by
    rw [h]
    change IsIso (𝟙 y)
    infer_instance
  have : IsIso (a.hom ≫ f) := inferInstanceAs (IsIso ((Over.map f).obj a).hom)
  have := hx a
  apply hnot
  have he : f = inv a.hom ≫ (a.hom ≫ f) := by simp
  rw [he]
  infer_instance
/-- 概要：構造射が全て可逆な over 圏から非可逆な単射への後合成の nerve は anodyne。
方針：恒等射の始対象性と終域の恒等射の終対象性を、終対象を付加する分解へ渡す。
規約：添字の射の Mono 性と非可逆性を省略しない。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma nerveOverMap_anodyne {x y : C} (f : x ⟶ y) [Mono f]
    (hnot : ¬ IsIso f) (hx : ∀ a : Over x, IsIso a.hom) :
    anodyneExtensions (nerveMap (Over.map f)) := by
  have : (Over.map f).Faithful :=
    { map_injective := fun {a b} g h e => by
        apply Over.OverMorphism.ext
        exact congrArg (fun k : (Over.map f).obj a ⟶ (Over.map f).obj b => k.left) e }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_anodyne_of_initial_terminal (Over.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.overMap_obj_injective f)
    (overId_initial_of_all_isIso x hx) (Over.mkIdTerminal (X := y))
    (overMap_misses_id f hnot hx)
/-- 概要：walking cospan の右端に入る射は可逆。
方針：右端に入る射の構成子は恒等射だけであることを使う。
規約：中央から右端へ向かう射はない。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma cospan_into_right_isIso {x : WalkingCospan} (f : x ⟶ .right) : IsIso f := by
  change WidePullbackShape.Hom x (.some WalkingPair.right) at f
  cases f
  change IsIso (𝟙 WalkingCospan.right)
  infer_instance
/-- 概要：持ち上げた walking cospan の右端に入る射は可逆。
方針：AsSmall.down で戻して可逆性を確認し、圏同値で反映する。
規約：対象と Hom の宇宙を係数の宇宙へ持ち上げる。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma resized_cospan_into_right_isIso {x : AsSmall.{u} WalkingCospan}
    (f : x ⟶ AsSmall.up.obj .right) : IsIso f := by
  have : IsIso (AsSmall.down.map f) := cospan_into_right_isIso (AsSmall.down.map f)
  have : (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_inverse
  exact isIso_of_reflects_iso f AsSmall.down
/-- 概要：持ち上げた walking cospan の右脚は可逆でない。
方針：逆射を AsSmall.down で戻すと中央から右端への存在しない射になることを使う。
規約：右脚は右端から中央へ向かう。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma resized_cospan_inr_not_isIso :
    ¬ IsIso (AsSmall.up.map WalkingCospan.Hom.inr :
      (AsSmall.up.obj .right : AsSmall.{u} WalkingCospan) ⟶ AsSmall.up.obj .one) := by
  intro h
  have := h
  have g : WalkingCospan.one ⟶ .right :=
    AsSmall.down.map (inv (AsSmall.up.map WalkingCospan.Hom.inr))
  change WidePullbackShape.Hom none (.some WalkingPair.right) at g
  cases g
/-- 概要：cospan の右脚による Bousfield–Kan 重みの実際の遷移は anodyne。
方針：右端の over 圏の構造射は可逆で、右脚は非可逆な単射であることを適用する。
規約：図式の右脚の fibration 性や重みの相対境界の結論は仮定しない。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の重みの遷移の比較。 -/
lemma bousfieldKanWeight_cospan_inr_anodyne :
    anodyneExtensions ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).map
      (AsSmall.up.map WalkingCospan.Hom.inr)) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  exact nerveOverMap_anodyne (AsSmall.up.map WalkingCospan.Hom.inr)
    resized_cospan_inr_not_isIso (fun a => resized_cospan_into_right_isIso a.hom)

/-- 概要：cospan の右脚の重みの像から作る相対的な点の錐の包含は anodyne。
方針：重みの遷移の単射性と anodyne 性を像の包含へ移し、相対錐の定理を適用する。
規約：元の重みの実際の遷移とその像を使い、別の同値な重みは選ばない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の元の重みから補助重みへの相対境界の表示。 -/
lemma bousfieldKanWeight_cospan_inr_relativeCone_anodyne :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary.{u} 0)
      (Subcomplex.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).map
        (AsSmall.up.map WalkingCospan.Hom.inr)))).ι := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_pointBoundary_range_anodyne _ bousfieldKanWeight_cospan_inr_anodyne

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
